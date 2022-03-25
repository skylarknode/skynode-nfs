'use strict';

const fsextra = require('fs-extra');
const _chokidar = require('chokidar');
const diskspace = require('diskspace');

var m_path = require('path');
var Promise = require('bluebird');
var util = require('util');
var fs = Promise.promisifyAll(require('fs'));
//var HTTPError = require('./HTTPError.js');
var async = require('async');
var mime = require('mime');
var moment = require('moment');
var crypto = require('crypto');
const mkdirp = require('mkdirp');
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
 * Secures a string for a command line search
 * strips: ", ', \, &, |, ;, -
 * @param string str
 * @return string
 */
var secureString = function secureString(str) {
  return str.replace(/"|'|\\|&|\||;|-/g, '')
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
 * Just wanted to test ES6 new stuff
 * ... just kidding extend one arg to another instead of only the first one
 * @param object origin
 * @param object ...add
 * @return origin
 */
var extend = function() {
  var add = [].slice.call(arguments)
  var origin = add.shift()

  for(let i in add) {
    origin = util._extend(origin, add[i]) 
  }

  return origin
}

/**
 * Build an URL string from params
 * this is used by the view to generate correct paths according to 
 * the sort, order, pages, search etc.
 * @param string path
 * @param string search
 * @param object options - will be built to a query key=value
 */
var buildUrl = function(path, search, options) {

  var str = ''
  var first = true

  for(let i in options) {
    if(options[i]) {
      str += first ? '?' : '&'
      str += i + '=' + options[i]
      first = false
    }
  }

  if(search) {
    return '/search' + str + '&search=' + search + '&path=' + encodeURIComponent(m_path.normalize(path))
  }

  return '/' + str + '&path=' + encodeURIComponent(m_path.normalize(path))
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
 * firstExistingPath
 * Get back the first path that does exist
 * @param array paths 
 * @return string the founded path
 */
var firstExistingPath = function(paths) {
  for(let i in paths) {
    if(paths[i] && existsSync(paths[i])) {
      return paths[i]
    }
  }

  return false
}

/**
 * Remove directory content with rimraf on each file
 * Skips dot files
 * @todo test?
 * @param string path
 * @return Promise
 */
var removeDirectoryContent = function(path) {
  return fs.readdirAsync(path)
  .filter(noDotFiles)
  .map(function(filename) {
    return rimraf(m_path.resolve(path, filename))
  })
}

/**
 * Handles system error, usually a Promise.catch
 * @param function next middleware next
 * @return function called by a Promise.catch
 */
var handleSystemError = function(next) {
   return function(e) {
   
     console.error(e.stack)

     return next(e);
     //return next(new HTTPError('A server error occur, if this happens again please contact the administrator: '+e.message, 500))
   }  
}

/**
 * Handles middlewares in parallel
 */
var parallelMiddlewares = function(middlewares) {
  return function(req, res, next) {
    return async.each(middlewares, function(m, cb) {
      return m(req, res, cb) 
    }, next) 
  }
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

/**
 * create sha1 hash from a string
 * @param string str the string to hash
 * @return string a sha1 hash in hexadecimal
 */
var sha1Hash = function(str) {
  var shasum = crypto.createHash('sha1')

  shasum.update(str, 'utf8')

  return shasum.digest('hex')
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
 * Build Breadcrumb from paths
 * @param string root
 * @param string path
 * @return array of objects {path, name} where name will be linked to path
 */
var buildBreadcrumb = function(root, path) {
  var breadcrumbs = [{path: root, name: root}]

  if(!path) {
    return breadcrumbs;
  }

  let paths = path.replace(root, '')
    .split('/')
    .filter(function(v) { return v != '' })

  for(let i in paths) {
    breadcrumbs[parseInt(i)+1] = {
      path: m_path.join(breadcrumbs[i].path, paths[i]),
      name: paths[i]
    }
  }

  return breadcrumbs
}

/**
 * @param string file
 * @param object root (@see pathInfo)
 * @param object options:
 *   - int maxDepth (10)
 *   - function filter (@see noDotFiles)
 */
var directorySize = function(file, root, options) {

  var path = m_path.resolve(root.path, file)
  var depth = file.split(m_path.sep).length

  if(root.depth < depth) {
    root.depth = depth
  }

  if(root.depth >= options.maxDepth) {
    root.depth = Infinity 
    return Promise.resolve(root)
  }

  return fs.statAsync(path).then(function(stat) {
    if(stat.isDirectory()) {
      let items = fs.readdirAsync(path);

      for(let i in options.filters) {
        items = items.filter(options.filters[i]) 
      }

      return items.each(v => directorySize(m_path.join(file, v), root, options));
    } else {
      root.size += stat.size
      return Promise.resolve(root)
    }
  }) 
  .catch(gracefulCatch(root, path))
}

var recursiveReaddir = function(root, options) {

  let items =  fs.readdirAsync(root);

  for(let i in options.filters) {
    items = items.filter(options.filters[i])
  }

  return items.map(function(f) {
    var path = m_path.join(root, f)

    return fs.statAsync(path).then(function(stat) {
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
 * Get directory size through cache
 * @param object options
 * @return function
 */
var getDirectorySize = function(options) {
  var cache = options.cache || false;

  /**
   * @param object file (see below)
   * @return Promise
   */
  return function calcDirectorySize(f) {

    if(f.ext !== 'app' && f.directory !== true) {
      return f
    }

    var hash = sha1Hash(f.path);

    var resolver = function() {
      if(cache) {
        return Promise.all([
          cache.time.put(hash, ''+f.mtime, options.cacheTTL),
          cache.size.put(hash, ''+f.size, options.cacheTTL)
        ]) .then(function() {
          return f;
        })
      }

      return f;
    }

    if(cache) {
      return cache.time.get(hash).then(function(cached) {
        if(cached == f.mtime) {
          return cache.size.get(hash)
          .then(function(size) {
            f.size = parseInt(size)
            return f
          })
        }

        return directorySize('', f, options).then(resolver);
      })
    }

    return directorySize('', f, options).then(resolver)
  }
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
    
    items = fs.readdirAsync(path);
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
 * Reads EXIF data
 */
function readExif(path, mime) {
  mime = mime || '';

  let _read = function defaultRead(resolve, reject) {
    resolve(null);
  };

  if ( mime.match(/^image/) ) {
    try {
      _read = function exifRead(resolve, reject) {
        /*eslint no-new: "off"*/
        new require('exif').ExifImage({image: path}, (err, result) => {
          if ( err ) {
            reject(err);
          } else {
            resolve(JSON.stringify(result, null, 4));
          }
        });
      };
    } catch ( e ) {}
  }

  return new Promise(_read);
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
  higherPath: higherPath,
  extend: extend,
  buildUrl: buildUrl,
  sanitize: sanitize,
  secureString: secureString,
  firstExistingPath: firstExistingPath,
  removeDirectoryContent: removeDirectoryContent,
  handleSystemError: handleSystemError,
  parallelMiddlewares: parallelMiddlewares,
  pathInfo: pathInfo,
  sha1Hash: sha1Hash,
  
  DATE_FORMAT : DATE_FORMAT, 
  DEFAULT_STAT : DEFAULT_STAT,
  W_OK : fs.W_OK,

  createReadStream : createReadStream,
  createWriteStream : createWriteStream,
  createWatch: createWatch,



  buildBreadcrumb : buildBreadcrumb,
  directorySize : directorySize,
  getDirectorySize : getDirectorySize,
  gracefulCatch : gracefulCatch,
  paths : paths,
  
  
  readExif : readExif,
  recursiveReaddir : recursiveReaddir,


  quoat : quoat,

  archive : archive,

  concat : concat,
  concatSync : concatSync,


  copyFile: fsextra.copyFile,
  copyFileSync: fsextra.copyFileSync,

  copydir: copydir,
  copydirSync: copydirSync,

  copy: fsextra.copy,
  copySync: fsextra.copySync,

  emptyDir: fsextra.emptyDir,
  emptyDirSync: fsextra.emptyDirSync,

  ensureFile: fsextra.ensureFile,
  ensureFileSync: fsextra.ensureFileSync,

  ensureDir: fsextra.ensureDir,
  ensureDirSync: fsextra.ensureDirSync,

  ensureLink: fsextra.ensureLink,
  ensureLinkSync: fsextra.ensureLinkSync,

  ensureSymlink: fsextra.ensureSymlink,
  ensureSymlinkSync: fsextra.ensureSymlinkSync,

  exists: exists,
  existsSync: existsSync,

  fstat : fsextra.fstat,
  fstatSync : fsextra.fstatSync,

  isEmpty : isEmpty,
  isEmptySync: isEmptySync,

  linkFile : linkFile,
  linkDir: linkDir,

  lstat : fsextra.lstat,
  lstatSync : fsextra.lstatSync,

  mkdir : fsextra.ensureDir,
  mkdirSync: fsextra.ensureDirSync,

  move : fsextra.move,
  moveSync: fsextra.moveSync,

  rmdir: rmdir,
  rmdirSync: rmdirSync,

  read: fsextra.read,
  readSync: fsextra.readSync,

  readdir : fsextra.readdir,
  readdirSync: fsextra.readdirSync,

  readFile : fsextra.readFile,
  readFileSync: fsextra.readFileSync,

  readJson : fsextra.readJson,
  readJsonSync: fsextra.readJsonSync,

  remove : fsextra.remove,
  removeSync: fsextra.removeSync,

  stat : fsextra.stat,
  statSync : fsextra.statSync,

  symlink : fsextra.symlink,
  symlinkSync: fsextra.symlinkSync,

  unlink  : fsextra.unlink,
  unlinkSync : fsextra.unlinkSync,

  walk : walk,

  write: fsextra.write,
  writeSync: fsextra.writeSync,


  writeFile: fsextra.writeFile,
  writeFileSync: fsextra.writeFile,

  writeJson : fsextra.writeJson,
  writeJsonSync: fsextra.writeJsonSync

}
