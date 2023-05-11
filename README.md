# `async.fnl`

A Fennel re-implementation of ClojureScript version of the [core.async](https://github.com/clojure/core.async) library.

## Releases and installation

This project follows the same version scheme the Clojure library, using MAJOR.MINOR.COMMITS starting from 1.6.
MAJOR and MINOR provide some relative indication of the size of the change, but do not follow semantic versioning.
In general, all changes endeavor to be non-breaking (by moving to new names rather than by breaking existing names).
COMMITS is an ever-increasing counter of commits since the beginning of this repository.

Copy [async.fnl](https://gitlab.com/andreyorst/async.fnl/-/raw/main/src/async.fnl) somewhere into your project.

## Differences from `core.async`

The Lua runtime doesn't require using inversion of control and complex code transformations to have the ability to pause funtion execution at any given moment.
Instead, Lua provides coroutines, that allow arbitrary control transfer to and from coroutines.
Hence, the library is coroutine-based, and all asynchronous facilities are built upon pausing thunks when operation occurs on the channel that is not ready.

The Lua runtime also doesn't provide any facilities for measuring time with precision higher than seconds by default.
If the [luasocket](https://aiq0.github.io/luasocket/index.html) or [luaposix](https://luaposix.github.io/luaposix/) libraries are available, they're used for time-tracking of the `timeout` channels.
Otherwise, Lua's [`os.time`](https://www.lua.org/manual/5.4/manual.html#pdf-os.time) is used, and the precision is limited to full seconds.
The library also depends on [`debug.sethook`](https://www.lua.org/manual/5.4/manual.html#pdf-debug.sethook) for running timers, and will disable `timeout` channels if the `debug` library is not present.

The library aims for providing full compatibility with ClojureScript version of the library.
Please report bugs or inconsistencies to the project [issue tracker](https://gitlab.com/andreyorst/async.fnl/-/issues).

## Documentation

The documentation is auto-generated with [Fenneldoc](https://gitlab.com/andreyorst/fenneldoc) and can be found [here](https://gitlab.com/andreyorst/async.fnl/-/blob/main/doc/src/async.md).

## Running tests

Run the following command at the root of the repository:

    fennel-test/runner tests/*.fnl

## Contributing

Please do.
You can report issues or feature request at project's GitLab repository.
Consider reading contribution guidelines beforehand.
