'use strict';

const fsextra = require('fs-extra-promise');
const _chokidar = require('chokidar');
const diskspace = require('diskspace');

var m_path = require('path');
var Promise = require('bluebird');
var fs = require('fs');
//var HTTPError = require('./HTTPError.js');
var async = require('async');
var mime = require('mime');
const rmdirp = require('rmdirp');
const copydirp = require('copy-dir');


const  archiver = require('archiver');



var MODE_0666 = parseInt('0666', 8);
var MODE_0755 = parseInt('0755', 8);


var rimraf = Promise.promisify(require('rimraf'));



/**
 * Filter names starting with a dot
 * @param string f
 * @return bool
 */
var noDotFiles = function(f) { 
  return !/^\./.test(m_path.basename(f)) 
}



/**
 * Get pack the higher available path to avoid unwanted behaviors
 * @param string root - usually req.user.home
 * @param string path - the path we want to go to
 * @return string - the higher path \o/
 */
var higherPath = function(root, path) {

  if(!root && typeof root != 'string')
    throw new TypeError('Root is not a string')

//  root = m_path.resolve(root)
  path = m_path.resolve(root, m_path.normalize(path) || './')

  if(path.length < root.length || path.indexOf(root) == -1) {
    path = root
  }

  return path
}


/**
 * Sanitize a string 
 * @see https://github.com/ezseed/watcher/blob/master/parser/movies.js#L27
 * @param string path
 */
var sanitize = function(path) {
  return m_path.basename(path)
     .replace(m_path.extname(path), '')
     .replace(new RegExp('-[a-z0-9]+$', 'i'), '') //team name
     .replace(/\-|_|\(|\)/g, ' ') //special chars
     .replace(/([\w\d]{2})\./ig, "$1 ") //Replacing dot with min 2 chars before
     .replace(/\.\.?([\w\d]{2})/ig, " $1")  //same with 2 chars after
     .replace(/part\s?\d{1}/ig, '') //part
     .replace(/\[[a-z0-9]+\]$/i, '')
     .replace(new RegExp(' {2,}', 'g'), ' ') //double space
}



/**
 * Give path informations
 * @param string path
 */
var pathInfo = function(path) {

  var filename = m_path.basename(path) 

  var o = {
    name: filename,
    ext: m_path.extname(filename),
    dirname: m_path.dirname(path),
    path: path
  }

  var m = mime.lookup(o.path).split('/')

  o.type = m[0]
  
  var filetype = m[1]
  
  if(~['.zip', '.rar', '.iso', '.tar'].indexOf(o.ext)) {
    o.type = 'archive'
  }

  if(!~['application', 'video', 'audio', 'image', 'text', 'archive'].indexOf(o.type)) {
    o.type = 'application'
  }

  return Promise.resolve(o) 
}


const DATE_FORMAT = 'llll'

const DEFAULT_STAT = {
  directory: false, 
  type: 'unknown',
  size: 0,
  mtime: 0,
  lastModified: '',
  atime: 0,
  lastAccessed: '',
  ctime: 0,
  lastChanged: '',
  depth: 0
}

var gracefulCatch = function(root, path) {
  return function(err) {

    if(err.code != 'EACCES' && err.code != 'ENOENT') {
      return Promise.reject(err)
    }

    if(err.code == 'EACCES')
      console.error('No file access (check rights on %s)', path)
    else
      console.error('No file entry (file %s does not exist ?!)', path)

    return Promise.resolve(root)
  }
}



/**
 * @param string file
 * @param object root (@see pathInfo)
 * @param object options:
 *   - int maxDepth (10)
 *   - function filter (@see noDotFiles)
 */
var capacity = function(file, root, options) {

  var path = m_path.resolve(root.path, file)
  var depth = file.split(m_path.sep).length

  if(root.depth < depth) {
    root.depth = depth
  }

  if(root.depth >= options.maxDepth) {
    root.depth = Infinity 
    return Promise.resolve(root)
  }

  return fsextra.statAsync(path).then(function(stat) {
    if(stat.isDirectory()) {
      let items = fsextra.readdirAsync(path);

      for(let i in options.filters) {
        items = items.filter(options.filters[i]) 
      }

      return items.each(v => capacity(m_path.join(file, v), root, options));
    } else {
      root.size += stat.size
      return Promise.resolve(root)
    }
  }) 
  .catch(gracefulCatch(root, path))
}

var recursiveReaddir = function(root, options) {

  let items =  fsextra.readdirAsync(root);

  for(let i in options.filters) {
    items = items.filter(options.filters[i])
  }

  return items.map(function(f) {
    var path = m_path.join(root, f)

    return fsextra.statAsync(path).then(function(stat) {
      let depth = root.replace(options.root, '').split(m_path.sep).length;

      if(depth > options.maxDepth)
        return path

      if(stat.isDirectory()) {
        return recursiveReaddir(path, options) 
      }

      return path
    })
    .catch(gracefulCatch(root, path))
  }).then(function(paths) {
    paths.push(root)
    return [].concat.apply([], paths)
  })
}



/**
 * Handles path argument and return filtered paths
 * @param mixed path
 * @param Object options {recursive: boolean}
 * @return array Promises
 */
var paths = function(path, options) {
  let items

  if(typeof path == 'string') {
    if(options.recursive === true) {
      return recursiveReaddir(path, options).map(function(e) {
        return m_path.relative(path, e);
      })
    }  
    
    items = fsextra.readdirAsync(path);
  } else if(Array.isArray(path)) {
    items = Promise.all(path);
  } else {
    throw new TypeError('Path must be an array or a string')
  }

  for(let i in options.filters) {
    items = items.filter(options.filters[i]);
  }

  return items;
}




/*
 * Create a read stream
 */
function createReadStream(filename, options) {
  return new Promise((resolve, reject) => {
    /*eslint new-cap: "off"*/
    try {
      const stream = fsextra.createReadStream(filename, Object.assign({
        bufferSize: 64 * 1024
      }, options));

      stream.on('error', (error) => {
        reject(error);
      });
      stream.on('open', () => {
        resolve(stream);
      });
    } catch ( e ) {
      reject(e);
    }
  });
}

/*
 * Create a write stream
 */
function createWriteStream(filename, options) {
  return new Promise((resolve, reject) => {
    /*eslint new-cap: "off"*/
    try {
      const stream = fsextra.createWriteStream(filename);

      stream.on('error', (error) => {
        reject(error);
      });
      stream.on('open', () => {
        resolve(stream);
      });
    } catch ( e ) {
      reject(e);
    }
  });
}

/*
 * Creates watch
 */
function createWatch(dir, callback) {

  _chokidar.watch(dir, {ignoreInitial: true, persistent: true}).on('all', (evname, wpath) => {
    if ( ['change', 'error'].indexOf(evname) === -1 ) {
      try {

        callback(dir,  {
          event:  evname,
          real: wpath
        });
      } catch ( e ) {
        console.warn(e, e.stack);
      }
    }
  });
}



/*----------------------------------------------------------------------------------------------------*/


function archive(sources,dest,options) {
  var zipper = archiver('zip',options);
  var self = this;

  return new Promise(function (resolve, reject) {
      console.log("archive:" + sources);
      zipper.on('error', function(err) {
        ///cconsole.log("err",err);
        ///zipper.abort();
        reject(err);
      });

      //on stream closed we can end the request
      zipper.on('end', function() {
        ///let b = zipper.pointer();
        ///debug('Archive wrote %d bytes', b);
        resolve();
      })


      if(typeof dest == 'string') {
        zipper.pipe(fs.createWriteStream(dest));
      } else {
        zipper.pipe(dest);
      }


      var directories = [],
          files = [];

      for (let i in sources) {
        var source = sources[i];
        if (fs.statSync(source).directory) {
          directories.push(source);
        } else {
          files.push(source);
        }
      }
      for(let i in directories) {
        console.log(directories[i], m_path.basename(directories[i]));
        zipper.directory(directories[i], m_path.basename(directories[i]));
      }

      for(let i in files) {
        ////zipper.append(_fs.createReadStream(files[i]), {name: m_path.basename(files[i])}) 
        zipper.file(files[i],{name: m_path.basename(files[i])})
      }

      zipper.finalize()
  });

}


function concat(data, callback) {
  if (data.files && data.files.length) {
    async.mapLimit(data.files, 1000, function (ref, next) {
      fsextra.readFile(ref.srcPath, ref.encode || 'utf8', function (err, file) {
        if (err) {
          return next(err);
        }

        next(null, file);
      });
    }, function (err, files) {
      if (err) {
        return callback(err);
      }

      var output = files.join('\n;');
      fsextra.writeFile(data.destPath, output, callback);
    });

    return;
  }

  callback();
}


function concatSync(data) {
  if (data.files && data.files.length) {
    let files = data.files.map(function (ref) {
      return fsextra.readFileSync(ref.srcPath, ref.encode || 'utf8');
    });
    let output = files.join('\n;');
    fsextra.writeFileSync(data.destPath, output);
  }
}


function copydir(from,to,filter,callback ) {
  function _copydir() {
    copydirp(from, to, filter,callback);   
  }

  if (callback) {
    _copydir();
  } else {
    return new Promise(function (resolve, reject) {
      callback = function(err,result) {
          if (err) {
            reject(err);
          } else {
            resolve(result);
          }
      };
      _copydir();
    });
  }
}

function copydirSync(from,to,filter) {
  return copydir.sync(from, to, filter);
}

function exists(path,callback) {
  function check(next) {
    fs.stat(path, function (err) {
      if (err) {
        if (err.code === 'ENOENT') {
          return callback(null, false);
        }
      }
      callback(err, true);
    });     
  }

  if (callback) {
    check(callback);
  } else {
    return new Promise(function(resolve, reject) {
      check(resolve);
    });    
  }
}


function existsSync(path) {
  try {
    fs.statSync(path);
  } catch (err) {
    if (err.code === 'ENOENT') {
      return false;
    }
    throw err;
  }

  return true;
}


/**
 * Check if the given directory `path` is empty.
 */

function isEmpty(path, callback) {
  function _checkEmpty() {
    fs.readdir(path, function(err, files) {
        if (err && err.code !== 'ENOENT') {
          callback(err);
        } else {
          callback(null,!files || !files.length);
        }
    });  
  }

  if (callback) {
    _checkEmpty();
  } else {
    return new Promise(function (resolve, reject) {
      callback = function(err,result) {
          if (err) {
            reject(err);
          } else {
            resolve(result);
          }
      };
      _checkEmpty();
    });
  }

}


function isEmptySync(path) {
    return fsextra.readdirSync(path).length === 0;
}


function linkDir(sourceDir, destDir, relative, callback) {
  if (!callback) {
    callback = relative;
    relative = false;
  }

  if (relative && process.platform !== 'win32') {
    sourceDir = path.relative(path.dirname(destDir), sourceDir);
  }

  var type = (process.platform === 'win32') ? 'junction' : 'dir';
  fs.symlink(sourceDir, destDir, type, callback);
}


function linkFile(filePath, destPath, relative, callback) {
  if (!callback) {
    callback = relative;
    relative = false;
  }

  if (relative && process.platform !== 'win32') {
    filePath = path.relative(path.dirname(destPath), filePath);
  }

  if (process.platform === 'win32') {
    fs.link(filePath, destPath, callback);
  } else {
    fs.symlink(filePath, destPath, 'file', callback);
  }
}

function quoat(path,callback) {
  function _quoat() {
      diskspace.check(path, (err, result) => {
        //result.total is how much the drive has totally.
        //result.used is how much of the drive is reported as used.
        //result.free is how much free space you have.
        //result.status isn't really that useful unless you want to debug.
        callback(err,result);
      });
  }

  if (callback) {
    _quoat();
  } else {
    return new Promise(function (resolve, reject) {
      callback = function(err,result){
        if (err) {
          reject(err);
        } else {
          resolve(result);
        }
      }; 
      _quoat();
    });    
  }
}

function rmdir(path,callback) {
  function _rmdir() {
    rmdirp(from, to, filter,callback);   
  }

  if (callback) {
    _rmdir();
  } else {
    return new Promise(function (resolve, reject) {
      callback = function(err,result) {
          if (err) {
            reject(err);
          } else {
            resolve(result);
          }
      };
      _rmdir();
    });
  }
      
}

function rmdirSync(path ) {
  return rmdirp.sync(path);
}


// Adapted from http://stackoverflow.com/questions/5827612/node-js-fs-readdir-recursive-directory-search
function  walk(dir, done) {
  var results = [];

  fsextra.readdir(dir, function (err, list) {
    if (err) {
      return done(err);
    }
    var pending = list.length;
    if (!pending) {
      return done(null, results);
    }
    list.forEach(function (filename) {
      filename = dir + '/' + filename;
      fsextra.stat(filename, function (err, stat) {
        if (err) {
          return done(err);
        }

        if (stat && stat.isDirectory()) {
          walk(filename, function (err, res) {
            if (err) {
              return done(err);
            }

            results = results.concat(res);
            pending -= 1;
            if (!pending) {
              done(null, results);
            }
          });
        } else {
          results.push(filename);
          pending -= 1;
          if (!pending) {
            done(null, results);
          }
        }
      });
    });
  });
};

module.exports = {
  noDotFiles: noDotFiles,
  
  DATE_FORMAT : DATE_FORMAT, 
  DEFAULT_STAT : DEFAULT_STAT,
  W_OK : fs.W_OK,

  createReadStream : createReadStream,
  createWriteStream : createWriteStream,
  createWatch: createWatch,


  // path 
  basename : m_path.basename,
  dirname : m_path.dirname,
  join : m_path.join,
  resolve : m_path.resolve,
  sep : m_path.sep,
  sanitize: sanitize,
  higherPath: higherPath,
  paths : paths,
  pathInfo: pathInfo,

  // file/directory
  quoatAsync : quoat,
  quoat : quoat,

  archiveAsync : archive,
  archive : archive,

  capacityAsync : capacity,
  capacity : capacity,

  concatAsync : concat,
  concat : concat,
  concatSync : concatSync,


  copyFileAsync: fsextra.copyFileAsync,
  copyFile: fsextra.copyFile,
  copyFileSync: fsextra.copyFileSync,

  copydirAsync: copydir,
  copydir: copydir,
  copydirSync: copydirSync,

  copyAsync: fsextra.copyAsync,
  copy: fsextra.copy,
  copySync: fsextra.copySync,

  emptyDirAsync: fsextra.emptyDirAsync,
  emptyDir: fsextra.emptyDir,
  emptyDirSync: fsextra.emptyDirSync,

  ensureFileAsync: fsextra.ensureFileAsync,
  ensureFile: fsextra.ensureFile,
  ensureFileSync: fsextra.ensureFileSync,

  ensureDirAsync: fsextra.ensureDirAsync,
  ensureDir: fsextra.ensureDir,
  ensureDirSync: fsextra.ensureDirSync,

  ensureLinkAsync: fsextra.ensureLinkAsync,
  ensureLink: fsextra.ensureLink,
  ensureLinkSync: fsextra.ensureLinkSync,

  ensureSymlinkAsync: fsextra.ensureSymlinkAsync,
  ensureSymlink: fsextra.ensureSymlink,
  ensureSymlinkSync: fsextra.ensureSymlinkSync,

  existsAsync: exists,
  exists: exists,
  existsSync: existsSync,

  fstatAsync : fsextra.fstatAsync,
  fstat : fsextra.fstat,
  fstatSync : fsextra.fstatSync,

  isEmptyAsync : isEmpty,
  isEmpty : isEmpty,
  isEmptySync: isEmptySync,

  linkFileAsync : linkFile,
  linkDir: linkDir,

  lstatAsync : fsextra.lstatAsync,
  lstat : fsextra.lstat,
  lstatSync : fsextra.lstatSync,

  mkdirAsync : fsextra.ensureDirAsync,
  mkdir : fsextra.ensureDir,
  mkdirSync: fsextra.ensureDirSync,

  moveAsync : fsextra.moveAsync,
  move : fsextra.move,
  moveSync: fsextra.moveSync,

  rmdirAsync: rmdir,
  rmdir: rmdir,
  rmdirSync: rmdirSync,

  readAsync: fsextra.readAsync,
  read: fsextra.read,
  readSync: fsextra.readSync,

  readdirAsync : fsextra.readdirAsync,
  readdir : fsextra.readdir,
  readdirSync: fsextra.readdirSync,

  readFileAsync : fsextra.readFileAsync,
  readFile : fsextra.readFile,
  readFileSync: fsextra.readFileSync,

  readJsonAsync : fsextra.readJsonAsync,
  readJson : fsextra.readJson,
  readJsonSync: fsextra.readJsonSync,

  recursiveReaddir : recursiveReaddir,

  removeAsync : fsextra.removeAsync,
  remove : fsextra.remove,
  removeSync: fsextra.removeSync,

  statAsync : fsextra.statAsync,
  stat : fsextra.stat,
  statSync : fsextra.statSync,

  symlinkAsync : fsextra.symlinkAsync,
  symlink : fsextra.symlink,
  symlinkSync: fsextra.symlinkSync,

  unlinkAsync  : fsextra.unlinkAsync,
  unlink  : fsextra.unlink,
  unlinkSync : fsextra.unlinkSync,

  walk : walk,

  writeAsync: fsextra.writeAsync,
  write: fsextra.write,
  writeSync: fsextra.writeSync,


  writeFileAsync: fsextra.writeFileAsync,
  writeFile: fsextra.writeFile,
  writeFileSync: fsextra.writeFileSync,

  writeJsonAsync : fsextra.writeJsonAsync,
  writeJson : fsextra.writeJson,
  writeJsonSync: fsextra.writeJsonSync

}
