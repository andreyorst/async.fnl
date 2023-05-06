# Async Macros (1.6.22)
Convenience macros for asynchronous programming.

**Table of contents**

- [`go`](#go)
- [`go-loop`](#go-loop)

## `go`
Function signature:

```
(go & body)
```

Asynchronously executes the `body`, returning immediately to the
calling thread. Additionally, any visible calls to `<!`, `>!` and
`alts!`  channel operations within the `body` will block (if
necessary) by 'parking' the calling thread rather than tying up the
only Lua thread.  Upon completion of the operation, the `body` will be
resumed.  Returns a channel which will receive the result of the `body`
when completed.

## `go-loop`
Function signature:

```
(go-loop bindings & body)
```

Asyncrhonous loop macro.

Similar to `let`, but binds a special `recur` call that will reassign
the values of the `bindings` and restart the loop `body` when called
in tail position.  Unlike `let`, doesn't support multiple-value
destructuring specifically.


---

Copyright (c) 2023 Andrey Listopadov

License: [EPL](https://gitlab.com/andreyorst/async.fnl/-/raw/master/LICENSE)


<!-- Generated with Fenneldoc v1.0.0
     https://gitlab.com/andreyorst/fenneldoc -->
