# Tiny Async

Pure Fennel asynchronous library, implementing channel-based communication without a scheduler.
The library is extremely limited, and largely callback based.
For a more featureful version see [fennel-async](https://gitlab.com/andreyorst/fennel-async).

## Installation

Copy [tiny-async.fnl](https://gitlab.com/andreyorst/tiny-async/-/raw/main/tiny-async.fnl) into your project.

## Usage

Require the library:

```fennel
(local {: chan : go : take! : put! : close!}
  (require :tiny-async))
```

Create a channel:

```fennel
(local c (chan))
```

Queue a take:

```fennel
(take! c (partial print :data:))
```

Queue a put:

```fennel
(put! c :val) ; prints "data: val"
```

### Go threads

A thread can be spawned with the `go` function:

```fennel
(go #(while true (print :data: (take! c))))
```

Now every `put!` to the channel `c` will print it's value.

Threads are automatically parked when `take!` or `put!` can't immediately succeed.
They are automatically resumed once the channel that parked the thread receives a value.

### Buffered channels

By default, `chan` creates an unbuffered channel.
All puts and takes will not succeed immediately, instead the thread is parked and assigned as a callback to the channel.

A channel can be given a buffer by providing a size argument to the `chan` function:

```fennel
(local bc (chan 3))
```

This channel can accept three puts without blocking the thread or queuing pending puts:

```fennel
(go #(do (put! bc 1) (print :done 1))) ; done 1
(go #(do (put! bc 2) (print :done 2))) ; done 2
(go #(do (put! bc 3) (print :done 3))) ; done 3
(go #(do (put! bc 4) (print :done 4))) ; put is now pending - go thread is parked
```

Taking from a buffered channel realizes pending puts (if any):

```fennel
(take! bc (partial print :data:))
;; prints: "done 4"
;; prints: "data: 1"
```

#### Unblocking buffers

A custom buffer can be provided to the channel to make it non-blocking.
For example, sliding and dropping buffers never block, instead the values are dropped from the buffers from either side:

```fennel
(local {: sliding-buffer
        : dropping-buffer
        : promise-buffer}
  (require :tiny-async))
(local sc (chan (sliding-buffer 3)))
(local dc (chan (dropping-buffer 3)))
```

Dropping buffer drops from the tail:

```fennel
(for [i 1 4] (put! dc i))
(take! dc print) ; 1
(take! dc print) ; 2
(take! dc print) ; 3
(take! dc print) ; nothing
```

Sliding buffer drops from the head:

```fennel
(for [i 1 4] (put! sc i))
(take! sc print) ; 2
(take! sc print) ; 3
(take! sc print) ; 4
(take! sc print) ; nothing
```

Promise buffer is a bit different, as it acts like a promise - it accepts only one value, dropping anything else, and it can't be emptied with a take:

```fennel
(local p (chan (promise-buffer)))
(put! p :val)
(take! p print) ; val
(put! p :other)
(take! p print) ; val
```

### Timeout channels

A `timeout` channel is automatically closed once a certain amount of time passes.

## Documentation

The documentation is auto-generated with Fenneldoc and can be found here.

## Contributing

Please do.
You can report issues or feature request at project's GitLab repository.
Consider reading contribution guidelines beforehand.
