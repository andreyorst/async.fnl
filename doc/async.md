# Async.fnl (1.6.20)
A Fennel library providing facilities for async programming and communication.

**Table of contents**

- [`buffer`](#buffer)
- [`dropping-buffer`](#dropping-buffer)
- [`sliding-buffer`](#sliding-buffer)
- [`promise-buffer`](#promise-buffer)
- [`unblocking-buffer?`](#unblocking-buffer)
- [`chan`](#chan)
- [`promise-chan`](#promise-chan)
- [`timeout`](#timeout)
- `<!`
- [`take!`](#take)
- `>!`
- [`put!`](#put)
- [`close!`](#close)
- [`go`](#go)
- [`alts!`](#alts)
- [`offer!`](#offer)
- [`poll!`](#poll)
- [`pipe`](#pipe)
- [`pipeline-async`](#pipeline-async)
- [`pipeline`](#pipeline)
- [`reduce`](#reduce)
- [`transduce`](#transduce)
- [`split`](#split)
- [`onto-chan!`](#onto-chan)
- [`to-chan!`](#to-chan)
- [`mult`](#mult)
- [`tap`](#tap)
- [`untap`](#untap)
- [`untap-all`](#untap-all)
- [`mix`](#mix)
- [`admix`](#admix)
- [`unmix`](#unmix)
- [`unmix-all`](#unmix-all)
- [`toggle`](#toggle)
- [`solo-mode`](#solo-mode)
- [`pub`](#pub)
- [`sub`](#sub)
- [`unsub`](#unsub)
- [`unsub-all`](#unsub-all)
- [`map`](#map)
- [`merge`](#merge)
- [`into`](#into)
- [`take`](#take-1)
- [`DroppingBuffer.empty?`](#droppingbufferempty)
- [`DroppingBuffer.full?`](#droppingbufferfull)
- [`DroppingBuffer.length`](#droppingbufferlength)
- [`DroppingBuffer.put`](#droppingbufferput)
- [`DroppingBuffer.take`](#droppingbuffertake)
- [`FixedBuffer.empty?`](#fixedbufferempty)
- [`FixedBuffer.full?`](#fixedbufferfull)
- [`FixedBuffer.length`](#fixedbufferlength)
- [`FixedBuffer.put`](#fixedbufferput)
- [`FixedBuffer.take`](#fixedbuffertake)
- [`PromiseBuffer.empty?`](#promisebufferempty)
- [`PromiseBuffer.full?`](#promisebufferfull)
- [`PromiseBuffer.length`](#promisebufferlength)
- [`PromiseBuffer.put`](#promisebufferput)
- [`PromiseBuffer.take`](#promisebuffertake)
- [`SlidingBuffer.empty?`](#slidingbufferempty)
- [`SlidingBuffer.full?`](#slidingbufferfull)
- [`SlidingBuffer.length`](#slidingbufferlength)
- [`SlidingBuffer.put`](#slidingbufferput)
- [`SlidingBuffer.take`](#slidingbuffertake)

## `buffer`
Function signature:

```
(buffer n)
```

Returns a fixed buffer of size `n`.  When full, puts will block/park.

## `dropping-buffer`
Function signature:

```
(dropping-buffer n)
```

Returns a buffer of size `n`.  When full, puts will complete but
val will be dropped (no transfer).

## `sliding-buffer`
Function signature:

```
(sliding-buffer n)
```

Returns a buffer of size `n`.  When full, puts will complete, and be
buffered, but oldest elements in buffer will be dropped (not
transferred).

## `promise-buffer`
Function signature:

```
(promise-buffer)
```

Create a promise buffer.

When the buffer receives a value all other values are dropped.  Taking
a value from the buffer doesn't remove it from the buffer.

## `unblocking-buffer?`
Function signature:

```
(unblocking-buffer? buff)
```

Returns true if a channel created with `buff` will never block.  That is
to say, puts into this buffer will never cause the buffer to be full.

## `chan`
Function signature:

```
(chan buf-or-n xform err-handler)
```

Creates a channel with an optional buffer, an optional
transducer, and an optional error handler.  If `buf-or-n` is a number,
will create and use a fixed buffer of that size.  If `xform` is
supplied a buffer must be specified.  `err-handler` must be a fn of one
argument - if an exception occurs during transformation it will be
called with the thrown value as an argument, and any non-nil return
value will be placed in the channel.

## `promise-chan`
Function signature:

```
(promise-chan xform err-handler)
```

Creates a promise channel with an optional transducer, and an optional
exception-handler.  A promise channel can take exactly one value that
consumers will receive.  Once full, puts complete but val is
dropped (no transfer).  Consumers will block until either a value is
placed in the channel or the channel is closed.  See [`chan`](#chan) for the
semantics of `xform` and `err-handler`.

## `timeout`
Function signature:

```
(timeout msecs)
```

Returns a channel that will close after `msecs`.

Note, this requires `debug.sethook` to be present.  By default, Lua
doesn't support sub-second time measurements.  Unless luasocket or
luaposix is available all millisecond values are rounded to the next
whole second value.

## `<!`
Function signature:

```
(<! port)
```

Takes a value from `port`.  Must be called inside a `(go ...)` block.
Will return `nil` if closed.  Will park if nothing is available.

## `take!`
Function signature:

```
(take! port fn1 on-caller?)
```

Asynchronously takes a value from `port`, passing to `fn1`.  Will pass
`nil` if closed.  If `on-caller?` (default `true`) is `true`, and value
is immediately available, will call `fn1` on calling thread.  Returns
`nil`.

## `>!`
Function signature:

```
(>! port val)
```

Puts a `val` into `port`.  `nil` values are not allowed.  Must be
called inside a `(go ...)` block.  Will park if no buffer space is
available.  Returns `true` unless `port` is already closed.

## `put!`
Function signature:

```
(put! port val fn1 on-caller?)
```

Asynchronously puts a `val` into `port`, calling `fn1` (if supplied)
when complete.  `nil` values are not allowed.  If
`on-caller?` (default `true`) is `true`, and the put is immediately
accepted, will call `fn1` on calling thread.

## `close!`
Function signature:

```
(close! port)
```

Close `port`.

## `go`
Function signature:

```
(go fn1)
```

Asynchronously executes the `fn1`, returning immediately to the
calling thread.  Additionally, any visible calls to `<!', `>!' and
[`alts!`](#alts)  channel operations within the body will block (if necessary)
by 'parking' the calling thread rather than tying up the only Lua
thread.  Upon completion of the operation, the `fn1` will be resumed.
Returns a channel which will receive the result of the `fn1` when
completed

## `alts!`
Function signature:

```
(alts! ports opts)
```

Completes at most one of several channel operations.  Must be called
inside a (go ...) block.  `ports` is a vector of channel endpoints,
which can be either a channel to take from or a vector of
[channel-to-put-to val-to-put], in any combination.  Takes will be made
as if by <!, and puts will be made as if by >!.  Unless the :priority
option is true, if more than one port operation is ready a
non-deterministic choice will be made.  If no operation is ready and a
:default value is supplied, [default-val :default] will be returned,
otherwise alts! will park until the first operation to become ready
completes.  Returns [val port] of the completed operation, where val is
the value taken for takes, and a boolean (true unless already closed,
as per put!) for puts.

`opts` are passed as :key val ...

Supported options:

:default val - the value to use if none of the operations are immediately ready
:priority true - (default nil) when true, the operations will be tried in order.

Note: there is no guarantee that the port exps or val exprs will be
used, nor in what order should they be, so they should not be
depended upon for side effects.

## `offer!`
Function signature:

```
(offer! port val)
```

Puts a `val` into `port` if it's possible to do so immediately.
`nil` values are not allowed.  Never blocks.  Returns `true` if offer
succeeds.

## `poll!`
Function signature:

```
(poll! port)
```

Takes a value from `port` if it's possible to do so immediately.
Never blocks.  Returns value if successful, `nil` otherwise.

## `pipe`
Function signature:

```
(pipe from to close?)
```

Takes elements from the `from` channel and supplies them to the `to`
channel.  By default, the to channel will be closed when the from
channel closes, but can be determined by the `close?` parameter.  Will
stop consuming the from channel if the to channel closes.

## `pipeline-async`
Function signature:

```
(pipeline-async n to af from close?)
```

Takes elements from the `from` channel and supplies them to the `to`
channel, subject to the async function `af`, with parallelism `n`.
`af` must be a function of two arguments, the first an input value and
the second a channel on which to place the result(s).  The presumption
is that `af` will return immediately, having launched some
asynchronous operation whose completion/callback will put results on
the channel, then [`close!`](#close) it.  Outputs will be returned in order
relative to the inputs.  By default, the `to` channel will be closed
when the `from` channel closes, but can be determined by the `close?`
parameter.  Will stop consuming the `from` channel if the `to` channel
closes.  See also [`pipeline`](#pipeline).

## `pipeline`
Function signature:

```
(pipeline n to xf from close? err-handler)
```

Takes elements from the `from` channel and supplies them to the `to`
channel, subject to the transducer `xf`, with parallelism `n`.
Because it is parallel, the transducer will be applied independently
to each element, not across elements, and may produce zero or more
outputs per input.  Outputs will be returned in order relative to the
inputs.  By default, the `to` channel will be closed when the `from`
channel closes, but can be determined by the `close?` parameter.  Will
stop consuming the `from` channel if the `to` channel closes.  Note
this is supplied for API compatibility with the Clojure version.
Values of `n > 1` will not result in actual concurrency in a
single-threaded runtime.  `err-handler` must be a fn of one argument -
if an exception occurs during transformation it will be called with
the thrown value as an argument, and any non-nil return value will be
placed in the channel.

## `reduce`
Function signature:

```
(reduce f init ch)
```

`f` should be a function of 2 arguments.  Returns a channel containing
the single result of applying `f` to `init` and the first item from the
channel, then applying `f` to that result and the 2nd item, etc.  If
the channel closes without yielding items, returns `init` and `f` is not
called.  `ch` must close before `reduce` produces a result.

## `transduce`
Function signature:

```
(transduce xform f init ch)
```

Async/reduces a channel with a transformation `xform` applied to `f`.
Usees `init` as initial value for [`reduce`](#reduce).  Returns a channel
containing the result.  `ch` must close before `transduce` produces a
result.

## `split`
Function signature:

```
(split p ch t-buf-or-n f-buf-or-n)
```

Takes a predicate `p` and a source channel `ch` and returns a vector
of two channels, the first of which will contain the values for which
the predicate returned true, the second those for which it returned
false.

The out channels will be unbuffered by default, or `t-buf-or-n` and
`f-buf-or-n` can be supplied.  The channels will close after the
source channel has closed.

## `onto-chan!`
Function signature:

```
(onto-chan! ch coll close?)
```

Puts the contents of `coll` into the supplied channel `ch`.
By default the channel will be closed after the items are copied, but
can be determined by the `close?` parameter.  Returns a channel which
will close after the items are copied.

## `to-chan!`
Function signature:

```
(to-chan! coll)
```

Creates and returns a channel which contains the contents of `coll`,
closing when exhausted.

## `mult`
Function signature:

```
(mult ch)
```

Creates and returns a mult(iple) of the supplied channel
`ch`.  Channels containing copies of the channel can be created with
'tap', and detached with 'untap'.

Each item is distributed to all taps in parallel and synchronously,
i.e. each tap must accept before the next item is distributed.  Use
buffering/windowing to prevent slow taps from holding up the mult.

Items received when there are no taps get dropped.

If a tap puts to a closed channel, it will be removed from the mult.

## `tap`
Function signature:

```
(tap mult ch close?)
```

Copies the `mult` source onto the supplied channel `ch`.
By default the channel will be closed when the source closes, but can
be determined by the `close?` parameter.

## `untap`
Function signature:

```
(untap mult ch)
```

Disconnects a target channel `ch` from a `mult`.

## `untap-all`
Function signature:

```
(untap-all mult)
```

Disconnects all target channels from a `mult`.

## `mix`
Function signature:

```
(mix out)
```

Creates and returns a mix of one or more input channels which will
be put on the supplied `out` channel.  Input sources can be added to
the mix with 'admix', and removed with 'unmix'.  A mix supports
soloing, muting and pausing multiple inputs atomically using 'toggle',
and can solo using either muting or pausing as determined by
'solo-mode'.

Each channel can have zero or more boolean modes set via 'toggle':

:solo - when `true`, only this (ond other soloed) channel(s) will
        appear in the mix output channel.  `:mute` and `:pause` states
        of soloed channels are ignored.  If solo-mode is `:mute`,
        non-soloed channels are muted, if `:pause`, non-soloed
        channels are paused.
:mute - muted channels will have their contents consumed but not
        included in the mix
:pause - paused channels will not have their contents consumed (and
         thus also not included in the mix)

## `admix`
Function signature:

```
(admix mix ch)
```

Adds `ch` as an input to the `mix`.

## `unmix`
Function signature:

```
(unmix mix ch)
```

Removes `ch` as an input to the `mix`.

## `unmix-all`
Function signature:

```
(unmix-all mix)
```

Removes all inputs from the `mix`.

## `toggle`
Function signature:

```
(toggle mix state-map)
```

Atomically sets the state(s) of one or more channels in a `mix`.  The
`state-map` is a map of channels -> channel-state-map.  A
channel-state-map is a map of attrs -> boolean, where attr is one or
more of `:mute`, `:pause` or `:solo`.  Any states supplied are merged
with the current state.

Note that channels can be added to a `mix` via [`toggle`](#toggle), which can be
used to add channels in a particular (e.g. paused) state.

## `solo-mode`
Function signature:

```
(solo-mode mix mode)
```

Sets the solo mode of the `mix`.  `mode` must be one of `:mute` or
`:pause`.

## `pub`
Function signature:

```
(pub ch topic-fn buf-fn)
```

Creates and returns a pub(lication) of the supplied channel `ch`,
partitioned into topics by the `topic-fn`.  `topic-fn` will be applied
to each value on the channel and the result will determine the 'topic'
on which that value will be put.  Channels can be subscribed to
receive copies of topics using 'sub', and unsubscribed using 'unsub'.
Each topic will be handled by an internal mult on a dedicated channel.
By default these internal channels are unbuffered, but a `buf-fn` can
be supplied which, given a topic, creates a buffer with desired
properties.  Each item is distributed to all subs in parallel and
synchronously, i.e. each sub must accept before the next item is
distributed.  Use buffering/windowing to prevent slow subs from
holding up the pub.  Items received when there are no matching subs
get dropped.  Note that if `buf-fns` are used then each topic is
handled asynchronously, i.e. if a channel is subscribed to more than
one topic it should not expect them to be interleaved identically with
the source.

## `sub`
Function signature:

```
(sub pub topic ch close?)
```

Subscribes a channel `ch` to a `topic` of a `pub`.
By default the channel will be closed when the source closes, but can
be determined by the `close?` parameter.

## `unsub`
Function signature:

```
(unsub pub topic ch)
```

Unsubscribes a channel `ch` from a `topic` of a `pub`.

## `unsub-all`
Function signature:

```
(unsub-all pub topic)
```

Unsubscribes all channels from a `pub`, or a `topic` of a `pub`.

## `map`
Function signature:

```
(map f chs buf-or-n)
```

Takes a function and a collection of source channels `chs`, and
returns a channel which contains the values produced by applying `f`
to the set of first items taken from each source channel, followed by
applying `f` to the set of second items from each channel, until any
one of the channels is closed, at which point the output channel will
be closed.  The returned channel will be unbuffered by default, or a
`buf-or-n` can be supplied.

## `merge`
Function signature:

```
(merge chs buf-or-n)
```

Takes a collection of source channels `chs` and returns a channel which
contains all values taken from them.  The returned channel will be
unbuffered by default, or a `buf-or-n` can be supplied.  The channel
will close after all the source channels have closed.

## `into`
Function signature:

```
(into t ch)
```

Returns a channel containing the single (collection) result of the
items taken from the channel `ch` conjoined to the supplied collection
`t`.  `ch` must close before `into` produces a result.

## `take`
Function signature:

```
(take n ch buf-or-n)
```

Returns a channel that will return, at most, `n` items from
`ch`.  After n items have been returned, or `ch` has been closed, the
return chanel will close.  The output channel is unbuffered by
default, unless `buf-or-n` is given.

## `DroppingBuffer.empty?`
Function signature:

```
(DroppingBuffer.empty? {:buf buffer})
```

Return `true` if `buffer` is empty.

## `DroppingBuffer.full?`
Function signature:

```
(DroppingBuffer.full?)
```

Check if buffer is full.
Always returns `false`.

## `DroppingBuffer.length`
Function signature:

```
(DroppingBuffer.length {:buf buffer})
```

Return item count in the `buffer`.

## `DroppingBuffer.put`
Function signature:

```
(DroppingBuffer.put {:buf buffer :size size} val)
```

Put `val` into the `buffer` if item count is less than `size`,
otherwise drop the value.

## `DroppingBuffer.take`
Function signature:

```
(DroppingBuffer.take {:buf buffer})
```

Take value from the `buffer`.

## `FixedBuffer.empty?`
Function signature:

```
(FixedBuffer.empty? {:buf buffer})
```

Return `true` if `buffer` is empty.

## `FixedBuffer.full?`
Function signature:

```
(FixedBuffer.full? {:buf buffer :size size})
```

Retrurn `true` if `buffer` length is equal to its `size` field.

## `FixedBuffer.length`
Function signature:

```
(FixedBuffer.length {:buf buffer})
```

Return item count in the `buffer`.

## `FixedBuffer.put`
Function signature:

```
(FixedBuffer.put {:buf buffer :size size} val)
```

Put `val` into the `buffer`.  Returns `true` if buffer has less than
`size` items.  Returns `false` if `buffer` is full.

## `FixedBuffer.take`
Function signature:

```
(FixedBuffer.take {:buf buffer})
```

Take value from the `buffer`.

## `PromiseBuffer.empty?`
Function signature:

```
(PromiseBuffer.empty? {:buf buffer})
```

Return `true` if `buffer` is empty.

## `PromiseBuffer.full?`
Function signature:

```
(PromiseBuffer.full? {:buf [val]})
```

Check if buffer has a value `val`.

## `PromiseBuffer.length`
Function signature:

```
(PromiseBuffer.length {:buf buffer})
```

Return item count in the `buffer`.

## `PromiseBuffer.put`
Function signature:

```
(PromiseBuffer.put {:buf buffer} val)
```

Put `val` into the `buffer` if there isnt one already,
otherwise drop the value.

## `PromiseBuffer.take`
Function signature:

```
(PromiseBuffer.take {:buf [val]})
```

Take value from the buffer.
Doesn't remove the `val` from the buffer.

## `SlidingBuffer.empty?`
Function signature:

```
(SlidingBuffer.empty? {:buf buffer})
```

Return `true` if `buffer` is empty.

## `SlidingBuffer.full?`
Function signature:

```
(SlidingBuffer.full?)
```

Check if buffer is full.
Always returns `false`.

## `SlidingBuffer.length`
Function signature:

```
(SlidingBuffer.length {:buf buffer})
```

Return item count in the `buffer`.

## `SlidingBuffer.put`
Function signature:

```
(SlidingBuffer.put {:buf buffer :size size} val)
```

Put `val` into the `buffer` if item count is less than `size`,
otherwise drop the oldest value.

## `SlidingBuffer.take`
Function signature:

```
(SlidingBuffer.take {:buf buffer})
```

Take value from the `buffer`.


---

Copyright (c) 2023 Andrey Listopadov

License: [EPL](https://gitlab.com/andreyorst/async.fnl/-/raw/master/LICENSE)


<!-- Generated with Fenneldoc v1.0.0
     https://gitlab.com/andreyorst/fenneldoc -->
