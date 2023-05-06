(comment
 "Copyright (c) 2023 Andrey Listopadov and contributors.  All rights reserved.
The use and distribution terms for this software are covered by the Eclipse
Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php) which
can be found in the file LICENSE at the root of this distribution.  By using
this software in any fashion, you are agreeing to be bound by the terms of
this license.
You must not remove this notice, or any other, from this software.")

;;; Helpers

(local -lib-name
  (or ... "async"))

(local {: gethook : sethook}
  (case _G.debug
    {: gethook : sethook} {: gethook : sethook}
    _ (do (io.stderr:write
           "WARNING: debug library is unawailable.  "
           -lib-name " uses debug.sethook to advance timers.  "
           "Time-related features are disabled.\n")
          {})))

(fn -main-thread? []
  "Check if current thread is a main one and not a coroutine."
  (case (coroutine.running)
    nil true
    (_ true) true
    _ false))

(fn -register-hook [f]
  "Run function `f` on each function return and every 1000 instructions.
Appends the hook to existing one, if found, unless the hook is `f`."
  (when (and gethook sethook)
    (match (gethook)
      f nil
      nil (sethook f :r 1000)
      (hook mask count)
      (sethook
       (fn [...] (hook ...) (f ...))
       mask
       count))))

(macro defprotocol [name ...]
  `(local ,name
     ,(faccumulate [methods {} i 1 (select :# ...)]
        (let [method (select i ...)]
          (assert-compile (list? method) "expected method declaration")
          (let [[name arglist body] method]
            (assert-compile (sym? name) "expected named method" name)
            (assert-compile (sequence? arglist) (.. "expected arglist for method " (tostring name)) arglist)
            (assert-compile (= nil body) (.. "expected no body for method " (tostring name)) body)
            (doto methods
              (tset (tostring name) `#(<= $ ,(length arglist)))))))))

(macro reify [...]
  (let [index (gensym)
        protocols []
        actions '(do)]
    (var current nil)
    ((fn loop [x ...]
       (assert-compile (or (sym? x) (list? x)) "expected symbol or fnspec" x)
       (if (sym? x)
           (do (set current x)
               (table.insert protocols (tostring x)))
           (list? x)
           (let [[name & [arglist &as fnspec]] x]
             (assert-compile (sym? name) "expected method name" name)
             (assert-compile (sequence? arglist) "expected method arglist" arglist)
             (table.insert
              actions
              `(case (. ,current ,(tostring name))
                 f# (if (f# ,(length arglist))
                        (tset ,index ,(tostring name) (fn ,(unpack fnspec)))
                        (error ,(.. "arity mismatch for method " (tostring name))))
                 ,(sym :_) (error ,(.. "Protocol " (tostring current) " doesn't define method " (tostring name)))))))
       (when (not= 0 (select :# ...))
         (loop ...)))
     ...)
    `(let [,index {}]
       ,actions
       (setmetatable
        {}
        {:__index ,index
         :name "reify"
         :__fennelview
         #(.. "#<" (: (tostring $) :gsub "table:" "reify:")
              ": " ,(table.concat protocols ", ") ">")}))))

(fn -merge [t1 t2]
  "Returns a new table containing items from `t1` and `t2`, overriding
values from `t1` if same keys are present."
  (let [res {}]
    (collect [k v (pairs t1) :into res] k v)
    (collect [k v (pairs t2) :into res] k v)))

(fn -merge-with [f t1 t2]
  "Returns a new table containing items from `t1` and `t2`, if same keys
are present merge is done by calling `f` with both values."
  (let [res (collect [k v (pairs t1)] k v)]
    (collect [k v (pairs t2) :into res]
      (case (. res k)
	e (values k (f e v))
	nil (values k v)))))

(fn -make-callback [f active-f]
  (->> {:__call (fn [_ ...] (when (active-f) ((or f #nil) ...)))}
       (setmetatable {:active? active-f})))

(local -nop
  (-make-callback #nil #true))

(local -socket
  (match (pcall require :socket) (true s) s _ nil))

(local -posix
  (match (pcall require :posix) (true p) p _ nil))

(local (-time -time-type)
  (if (?. -socket :gettime)
      (values -socket.gettime :socket)
      (?. -posix :clock_gettime)
      (let [gettime -posix.clock_gettime]
        (values #(let [(s ns) (gettime)]
                   (+ s (/ ns 1000000000)))
                :posix))
      (values os.time :lua)))

(local -difftime
  (case -time-type
    (where (or :posix :socket)) #(- $1 $2)
    :lua os.difftime))

;;; Buffers

(local -buf {})

(local FixedBuffer
  {:type -buf
   :full? (fn [{:buf buffer : size}]
            "Retrurn `true` if `buffer` length is equal to its `size` field."
            (= (length buffer) size))
   :empty? (fn [{:buf buffer}]
             "Return `true` if `buffer` is empty."
             (= 0 (length buffer)))
   :length (fn [{:buf buffer}]
             "Return item count in the `buffer`."
             (length buffer))
   :put (fn [{:buf buffer : size} val]
          "Put `val` into the `buffer`.  Returns `true` if buffer has less than
`size` items.  Returns `false` if `buffer` is full."
          (assert (not= val nil) "value must not be nil")
          (let [len (length buffer)]
            (when (< len size)
              (tset buffer (+ 1 len) val)
              true)))
   :take (fn [{:buf buffer}]
           "Take value from the `buffer`."
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local DroppingBuffer
  {:type -buf
   :full? (fn []
            "Check if buffer is full.
Always returns `false`."
            false)
   :empty? (fn [{:buf buffer}]
             "Return `true` if `buffer` is empty."
             (= 0 (length buffer)))
   :length (fn [{:buf buffer}]
             "Return item count in the `buffer`."
             (length buffer))
   :put (fn [{:buf buffer : size} val]
          "Put `val` into the `buffer` if item count is less than `size`,
otherwise drop the value."
          (assert (not= val nil) "value must not be nil")
          (when (< (length buffer) size)
            (tset buffer (+ 1 (length buffer)) val))
          true)
   :take (fn [{:buf buffer}]
           "Take value from the `buffer`."
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local SlidingBuffer
  {:type -buf
   :full? (fn []
            "Check if buffer is full.
Always returns `false`."
            false)
   :empty? (fn [{:buf buffer}]
             "Return `true` if `buffer` is empty."
             (= 0 (length buffer)))
   :length (fn [{:buf buffer}]
             "Return item count in the `buffer`."
             (length buffer))
   :put (fn [{:buf buffer : size} val]
          "Put `val` into the `buffer` if item count is less than `size`,
otherwise drop the oldest value."
          (assert (not= val nil) "value must not be nil")
          (tset buffer (+ 1 (length buffer)) val)
          (when (< size (length buffer))
            (table.remove buffer 1))
          true)
   :take (fn [{:buf buffer}]
           "Take value from the `buffer`."
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local PromiseBuffer
  {:type -buf
   :full? (fn [{:buf [val]}]
            "Check if buffer has a value `val`."
            (not= nil val))
   :empty? (fn [{:buf buffer}]
             "Return `true` if `buffer` is empty."
             (= 0 (length buffer)))
   :length (fn [{:buf buffer}]
             "Return item count in the `buffer`."
             (length buffer))
   :put (fn [{:buf buffer} val]
          "Put `val` into the `buffer` if there isnt one already,
otherwise drop the value."
          (assert (not= val nil) "value must not be nil")
          (when (= 0 (length buffer))
            (tset buffer 1 val))
          true)
   :take (fn [{:buf [val]}]
           "Take value from the buffer.
Doesn't remove the `val` from the buffer."
           val)})

(fn -buffer [size buffer-type]
  (and size (assert (= :number (type size)) (.. "size must be a number: " (tostring size))))
  (assert (not (: (tostring size) :match "%.")) "size must be integer")
  (setmetatable
   {:size size
    :buf []}
   {:__index buffer-type
    :__name "buffer"
    :__fennelview
    #(.. "#<" (: (tostring $) :gsub "table:" "buffer:") ">")}))

(fn buffer [n]
  "Returns a fixed buffer of size `n`.  When full, puts will block/park."
  (-buffer n FixedBuffer))

(fn dropping-buffer [n]
  "Returns a buffer of size `n`.  When full, puts will complete but
val will be dropped (no transfer)."
  (-buffer n DroppingBuffer))

(fn sliding-buffer [n]
  "Returns a buffer of size `n`.  When full, puts will complete, and be
buffered, but oldest elements in buffer will be dropped (not
transferred)."
  (-buffer n SlidingBuffer))

(fn promise-buffer []
  "Create a promise buffer.

When the buffer receives a value all other values are dropped.  Taking
a value from the buffer doesn't remove it from the buffer."
  (-buffer 1 PromiseBuffer))

(fn -buffer? [obj]
  (match obj
    {:type -buf} true
    _ false))

(fn unblocking-buffer? [buff]
  "Returns true if a channel created with `buff` will never block.  That is
to say, puts into this buffer will never cause the buffer to be full."
  (match (and (-buffer? buff)
              (. (getmetatable buff) :__index))
    SlidingBuffer true
    DroppingBuffer true
    PromiseBuffer true
    _ false))

;;; Channels

(local -chan {})
(local -timeouts {})


(fn -chan? [obj]
  (match obj {:type -chan} true _ false))

(fn -advance-timeouts []
  "Close any timeout channels whose closing time is less than or equal
to current time."
  (when (next -timeouts)
    (let [to-remove (icollect [t ch (pairs -timeouts)]
                      (when (>= 0 (-difftime t (-time)))
                        (ch:close)
                        t))]
      (each [_ t (ipairs to-remove)]
        (tset -timeouts t nil)))))

(fn -make-thunk [thunk active-fn name]
  (->> {:__name name
        :__fennelview
        #(.. "#<" (: (tostring $) :gsub "table:" (.. name ":")) ">")}
       (setmetatable {:thunk thunk :active? active-fn})))

(fn -try-buffer [chan val callback]
  (when (or (not callback) (callback.active?))
    (case chan.buf
      (where buf (not (buf:full?)))
      (do (case chan.xform
            xform (xform buf val)
            nil (buf:put val))
          (when callback (callback true))
          true))))

(local Channel
  {:type -chan
   :put (fn [chan val callback enqueue?]
          (assert (not= val nil) "val must not be nil")
          (if chan.closed
              (do (callback false) false)
              (let [buffered? (-try-buffer chan val callback)]
                ((fn loop []
                   (case chan
                     (where {: takes} (next takes))
                     (let [take (table.remove takes 1)]
                       (if (and (callback.active?) (take.active?))
                           (do (callback true)
                               (case (coroutine.resume
                                      take.thunk
                                      (if buffered? (chan.buf:take) val))
                                 (false msg) (chan:err-handler msg))
                               true)
                           (loop)))
                     (where {: puts} (< (length puts) 1024))
                     (when (and (not buffered?) (callback.active?))
                       (if (or (-main-thread?) enqueue?)
                           (let [thunk (-make-thunk (->> (partial callback)
                                                         coroutine.create)
                                                    callback.active?
                                                    "put")]
                             (table.insert puts [thunk val]))
                           (let [thunk (-make-thunk (coroutine.running)
                                                    callback.active?
                                                    "put")]
                             (table.insert puts [thunk val])
                             (coroutine.yield)
                             (callback true)))
                       true)
                     _ (error "too many pending puts")))))))
   :take (fn loop [chan callback enqueue?]
           (assert (not= nil callback) "expected a callback")
           (let [res (case chan
                       (where {: buf} (not (buf:empty?)))
                       (when (callback.active?)
                         (let [val (buf:take)
                               len (buf:length)
                               puts chan.puts]
                           (callback val)
                           ((fn loop []
                              (case (table.remove puts 1)
                                put (let [[put val*] put]
                                      (if (put.active?)
                                          (let [_ (-try-buffer chan val*)
                                                len* (buf:length)]
                                            (case (coroutine.resume put.thunk)
                                              (false msg) (chan:err-handler msg))
                                            (when (= len len*)
                                              (loop)))
                                          (loop))))))
                           val))
                       (where {: puts} (next puts))
                       (let [[put val] (table.remove puts 1)]
                         (if (and (callback.active?) (put.active?))
                             (do (callback val)
                                 (case (coroutine.resume put.thunk)
                                   (false msg) (chan:err-handler msg))
                                 val)
                             (loop chan callback enqueue?)))
                       (where {: takes} (< (length takes) 1024))
                       (if chan.closed
                           (callback nil)
                           (when (callback.active?)
                             (if (or (-main-thread?) enqueue?)
                                 (table.insert takes (-make-thunk (coroutine.create #(do (callback $) $))
                                                                  callback.active?
                                                                  "take"))
                                 (let [thunk (-make-thunk (coroutine.running)
                                                          callback.active?
                                                          "take")
                                       _ (table.insert takes thunk)
                                       res (coroutine.yield)]
                                   (callback res)
                                   res))))
                       _ (error "too many pending takes"))]
             res))
   :close (fn [chan]
            (when (not chan.closed)
              (set chan.closed true)
              (while (> (length chan.takes) 0)
                (let [take (table.remove chan.takes 1)]
                  (when (take.active?)
                    (case (coroutine.resume take.thunk)
                      (false msg) (chan:err-handler msg)))))))})

(fn -err-handler [mesg]
  (io.stderr:write (tostring mesg) "\n")
  nil)

(fn chan [buf-or-n xform err-handler]
  "Creates a channel with an optional buffer, an optional
transducer, and an optional error handler.  If `buf-or-n` is a number,
will create and use a fixed buffer of that size.  If `xform` is
supplied a buffer must be specified.  `err-handler` must be a fn of one
argument - if an exception occurs during transformation it will be
called with the thrown value as an argument, and any non-nil return
value will be placed in the channel."
  (let [buffer (match buf-or-n
                 {:type -buf} buf-or-n
                 0 nil
                 size (buffer size))
        xform (when xform
                (assert (not= nil buffer) "buffer must be supplied when transducer is")
                (xform (fn [...]
                         (case (values (select :# ...) ...)
                           (1 buffer) buffer
                           (2 buffer val) (: buffer :put val)))))
        err-handler (or err-handler -err-handler)]
    (setmetatable
     {:puts []
      :takes []
      :buf buffer
      :xform xform
      :err-handler (fn [ch err]
                     (case (err-handler err)
                       res (ch:put ch res -nop)))}
     {:__index Channel
      :__name "channel"
      :__fennelview
      #(.. "#<" (: (tostring $) :gsub "table:" "channel:") ">")})))

(fn promise-chan [xform err-handler]
  "Creates a promise channel with an optional transducer, and an optional
exception-handler.  A promise channel can take exactly one value that
consumers will receive.  Once full, puts complete but val is
dropped (no transfer).  Consumers will block until either a value is
placed in the channel or the channel is closed.  See `chan' for the
semantics of `xform` and `err-handler`."
  (chan (promise-buffer) xform err-handler))

(var warned false)

(fn timeout [msecs]
  "Returns a channel that will close after `msecs`.

Note, this requires `debug.sethook` to be present.  By default, Lua
doesn't support sub-second time measurements.  Unless luasocket or
luaposix is available all millisecond values are rounded to the next
whole second value."
  (assert (and gethook sethook) "Can't advance timers - debug.sethook unavailable")
  (let [dt (case -time-type
             :lua (let [s (/ msecs 1000)
                        s* (math.ceil s)]
                    (when (and (not (= s* s)) (not warned))
                      (set warned true)
                      (: (timeout 10000) :take (-make-callback #(set warned false) #true) true)
                      (io.stderr:write
                       (.. "WARNING Lua doesn't support sub-second time precision.  "
                           "Timeout rounded to the next nearest whole second.  "
                           "Install luasocket or luaposix to get sub-second precision.\n")))
                    s*)
             _ (/ msecs 1000))
        t (+ (-time) dt)]
    (or (. -timeouts t)
        (let [c (chan)]
          (tset -timeouts t c)
          c))))

(fn take! [port fn1 ...]
  {:fnl/docstring "Asynchronously takes a value from `port`, passing to `fn1`.  Will pass
`nil` if closed.  If `on-caller?` (default `true`) is `true`, and value
is immediately available, will call `fn1` on calling thread.  Returns
`nil`."
   :fnl/arglist [port fn1 on-caller?]}
  (assert (-chan? port) "expected a channel as first argument")
  (assert (not= nil fn1) "expected a callback")
  (let [on-caller? (if (= (select :# ...) 0) true ...)]
    (port:take
     (-make-callback fn1 #true)
     (and fn1 on-caller?))
    nil))

(fn <!! [port]
  "Takes a value from `port`.  Will return `nil` if closed.  Will block
if nothing is available.  Not intended for use in direct or transitive
calls from `(go ...)` blocks."
  (assert (-main-thread?) "<!! used not on the main thread")
  (var val nil)
  (port:take (-make-callback #(do (pprint :res $) (set val $)) #true) true)
  (while (and (= val nil) (not port.closed)))
  val)

(fn <! [port]
  "Takes a value from `port`.  Must be called inside a `(go ...)` block.
Will return `nil` if closed.  Will park if nothing is available."
  (assert (not (-main-thread?)) "<! used not in (go ...) block")
  (assert (-chan? port) "expected a channel as first argument")
  (port:take -nop false))

(fn put! [port val fn1 ...]
  {:fnl/docstring "Asynchronously puts a `val` into `port`, calling `fn1` (if supplied)
when complete.  `nil` values are not allowed.  If
`on-caller?` (default `true`) is `true`, and the put is immediately
accepted, will call `fn1` on calling thread."
   :fnl/arglist [port val fn1 on-caller?]}
  (assert (-chan? port) "expected a channel as first argument")
  (let [on-caller? (if (= (select :# ...) 0) true ...)]
    (port:put val (-make-callback fn1 #true) (not on-caller?))))

(fn >!! [port val]
  "Puts a `val` into `port`.  `nil` values are not allowed. Will block if no
buffer space is available.  Returns `true` unless `port` is already
closed.  Not intended for use in direct or transitive calls from `(go
...)` blocks."
  (assert (-main-thread?) ">!! used not on the main thread")
  (var (not-done res) true)
  (port:put
   val
   (-make-callback
    #(set (not-done res) (values false $))
    #true)
   true)
  (while not-done)
  res)

(fn >! [port val]
  "Puts a `val` into `port`.  `nil` values are not allowed.  Must be
called inside a `(go ...)` block.  Will park if no buffer space is
available.  Returns `true` unless `port` is already closed."
  (assert (not (-main-thread?)) ">! used not in (go ...) block")
  (port:put val -nop false))

(fn close! [port]
  "Close `port`."
  (assert (-chan? port) "expected a channel")
  (port:close))

(fn go* [fn1]
  "Asynchronously executes the `fn1`, returning immediately to the
calling thread.  Additionally, any visible calls to `<!', `>!' and
`alts!'  channel operations within the body will block (if necessary)
by 'parking' the calling thread rather than tying up the only Lua
thread.  Upon completion of the operation, the `fn1` will be resumed.
Returns a channel which will receive the result of the `fn1` when
completed"
  (let [c (chan 1)]
    (case (-> (fn []
                (case (fn1)
                  val (>! c val))
                (close! c))
              coroutine.create
              coroutine.resume)
      (false msg) (error msg))
    c))

(macro go [...]
  "Private helper, see `async-macros.fnl` for public macro."
  `(go* (fn [] ,...)))

(macro go-loop [bindings ...]
  "Private helper, see `async-macros.fnl` for public macro.
Doesn't have support for sequential binding!"
  (let [syms (fcollect [i 1 (length bindings) 2] (. bindings i))
        vals (fcollect [i 2 (length bindings) 2] (. bindings i))
        recur (sym :recur)]
    (if (next vals)
        `(go* #((fn ,recur ,syms ,...)
                ,(unpack vals)))
        `(go* (fn ,recur [] ,...)))))

(fn -random-array [n]
  (let [ids (fcollect [i 1 n] i)]
    (for [i n 2 -1]
      (let [j (math.random i)
            ti (. ids i)]
        (tset ids i (. ids j))
        (tset ids j ti)))
    ids))

(fn alts! [ports opts]
  "Completes at most one of several channel operations.  Must be called
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
depended upon for side effects."
  (assert (not (-main-thread?)) "called alts! on the main thread")
  (let [n (length ports)
        ids (-random-array n)
        res-ch (chan (promise-buffer))
        state {:active? true}]
    (for [i 1 n]
      (let [id (if (and opts opts.priority) i (. ids i))]
        (case (. ports id)
          [c ?v] (c:put ?v
                        (-make-callback
                         #(let [res {1 $ 2 c}]
                            (set state.active? false)
                            (put! res-ch res)
                            (close! res-ch))
                         #state.active?)
                        true)
          c (c:take (-make-callback
                     #(let [res {1 $ 2 c}]
                        (set state.active? false)
                        (put! res-ch res)
                        (close! res-ch))
                     #state.active?)
                    true))))
    (if (and state.active?
             opts opts.default)
        (do (set state.active? false)
            [opts.default :default])
        (<! res-ch))))

(fn offer! [port val]
  "Puts a `val` into `port` if it's possible to do so immediately.
`nil` values are not allowed.  Never blocks.  Returns `true` if offer
succeeds."
  (assert (-chan? port) "expected a channel as first argument")
  (port:put val (-make-callback #nil #false) false))

(fn poll! [port]
  "Takes a value from `port` if it's possible to do so immediately.
Never blocks.  Returns value if successful, `nil` otherwise."
  (assert (-chan? port) "expected a channel")
  (port:take (-make-callback #nil #false) false))

;;; Operations

(fn pipe [from to ...]
  {:fnl/docstring "Takes elements from the `from` channel and supplies them to the `to`
channel.  By default, the to channel will be closed when the from
channel closes, but can be determined by the `close?` parameter.  Will
stop consuming the from channel if the to channel closes."
   :fnl/arglist [from to close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (go-loop []
      (let [val (<! from)]
        (if (= nil val)
            (when close? (close! to))
            (do (>! to val)
                (recur)))))))

(fn -pipeline [n to xf from close? err-handler kind]
  (let [jobs (chan n)
        results (chan n)
        finishes (and (= kind :async) (chan n))
        process (fn [job]
                  (case job
                    nil (do (close! results) nil)
                    [v p] (let [res (chan 1 xf err-handler)]
                            (go (>! res v)
                                (close! res))
                            (put! p res)
                            true)))
        async (fn [job]
                (case job
                  nil (do (close! results)
                          (close! finishes)
                          nil)
                  [v p] (let [res (chan 1)]
                          (xf v res)
                          (put! p res)
                          true)))]
    (for [_ 1 n]
      (case kind
        :compute (go-loop []
                   (let [job (<! jobs)]
                     (when (process job)
                       (recur))))
        :async (go-loop []
                 (let [job (<! jobs)]
                   (when (async job)
                     (<! finishes)
                     (recur))))))
    (go-loop []
      (match (<! from)
        nil (close! jobs)
        v (let [p (chan 1)]
            (>! jobs [v p])
            (>! results p)
            (recur))))
    (go-loop []
      (case (<! results)
        nil (when (not= close? false)
              (close! to))
        p (case (<! p)
            res (do ((fn loop* []
                       (case (<! res)
                         val (do (>! to val)
                                 (loop*)))))
                    (when finishes
                      (>! finishes :done))
                    (recur)))))))

(fn pipeline-async [n to af from ...]
  {:fnl/docstring "Takes elements from the `from` channel and supplies them to the `to`
channel, subject to the async function `af`, with parallelism `n`.
`af` must be a function of two arguments, the first an input value and
the second a channel on which to place the result(s).  The presumption
is that `af` will return immediately, having launched some
asynchronous operation whose completion/callback will put results on
the channel, then `close!' it.  Outputs will be returned in order
relative to the inputs.  By default, the `to` channel will be closed
when the `from` channel closes, but can be determined by the `close?`
parameter.  Will stop consuming the `from` channel if the `to` channel
closes.  See also `pipeline'."
   :fnl/arglist [n to af from close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (-pipeline n to af from close? nil :async)))

(fn pipeline [n to xf from ...]
  {:fnl/docstring "Takes elements from the `from` channel and supplies them to the `to`
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
placed in the channel."
   :fnl/arglist [n to xf from close? err-handler]}
  (let [(err-handler close?) (if (= (select :# ...) 0) true ...)]
    (-pipeline n to xf from close? err-handler :compute)))

(fn split [p ch t-buf-or-n f-buf-or-n]
  "Takes a predicate `p` and a source channel `ch` and returns a vector
of two channels, the first of which will contain the values for which
the predicate returned true, the second those for which it returned
false.

The out channels will be unbuffered by default, or `t-buf-or-n` and
`f-buf-or-n` can be supplied.  The channels will close after the
source channel has closed."
  (let [tc (chan t-buf-or-n)
        fc (chan f-buf-or-n)]
    (go-loop []
      (let [v (<! ch)]
        (if (= nil v)
            (do (close! tc) (close! fc))
            (when (>! (if (p v) tc fc) v)
              (recur)))))
    [tc fc]))

(fn reduce [f init ch]
  "`f` should be a function of 2 arguments.  Returns a channel containing
the single result of applying `f` to `init` and the first item from the
channel, then applying `f` to that result and the 2nd item, etc.  If
the channel closes without yielding items, returns `init` and `f` is not
called.  `ch` must close before `reduce` produces a result."
  (go-loop [ret init]
    (let [v (<! ch)]
      (if (= nil v) ret
          (recur (f ret v))))))

(fn transduce [xform f init ch]
  "Async/reduces a channel with a transformation `xform` applied to `f`.
Usees `init` as initial value for `reduce'.  Returns a channel
containing the result.  `ch` must close before `transduce` produces a
result."
  (let [f (xform f)]
    (go (let [ret (<! (reduce f init ch))]
          (f ret)))))

(fn onto-chan! [ch coll ...]
  {:fnl/docstring "Puts the contents of `coll` into the supplied channel `ch`.
By default the channel will be closed after the items are copied, but
can be determined by the `close?` parameter.  Returns a channel which
will close after the items are copied."
   :fnl/arglist [ch coll close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (go (each [_ v (ipairs coll)]
          (>! ch v))
        (when close? (close! ch))
        ch)))

(fn -bounded-length [bound t]
  (math.min bound (length t)))

(fn to-chan! [coll]
  "Creates and returns a channel which contains the contents of `coll`,
closing when exhausted."
  (let [ch (chan (-bounded-length 100 coll))]
    (onto-chan! ch coll)
    ch))

;;; Mult, Mix, Pub

(defprotocol Mux
  (muxch [_]))

(defprotocol Mult
  (tap [_ ch close?])
  (untap [_ ch])
  (untap-all [_]))

(fn mult [ch]
  "Creates and returns a mult(iple) of the supplied channel
`ch`.  Channels containing copies of the channel can be created with
'tap', and detached with 'untap'.

Each item is distributed to all taps in parallel and synchronously,
i.e. each tap must accept before the next item is distributed.  Use
buffering/windowing to prevent slow taps from holding up the mult.

Items received when there are no taps get dropped.

If a tap puts to a closed channel, it will be removed from the mult."
  (var dctr nil)
  (let [atom {:cs {}}
        m (reify
           Mux
           (muxch [_] ch)

           Mult
           (tap [_ ch close?] (tset atom :cs ch close?) nil)
           (untap [_ ch] (tset atom :cs ch nil) nil)
           (untap-all [_] (tset atom :cs {}) nil))
        dchan (chan 1)
        done (fn [_]
               (set dctr (- dctr 1))
               (when (= 0 dctr)
                 (put! dchan true)))]
    (go-loop []
      (let [val (<! ch)]
        (if (= nil val)
            (each [c close? (pairs atom.cs)]
              (when close? (close! c)))
            (let [chs (icollect [k (pairs atom.cs)] k)]
              (set dctr (length chs))
              (each [_ c (ipairs chs)]
                (when (not (put! c val done))
                  (m:untap* c)))
              ;;wait for all
              (when (next chs)
                (<! dchan))
              (recur)))))
    m))

(fn tap [mult ch ...]
  {:fnl/docstring "Copies the `mult` source onto the supplied channel `ch`.
By default the channel will be closed when the source closes, but can
be determined by the `close?` parameter."
   :fnl/arglist [mult ch close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (mult:tap ch close?) ch))

(fn untap [mult ch]
  "Disconnects a target channel `ch` from a `mult`."
  (mult:untap ch))

(fn untap-all [mult]
  "Disconnects all target channels from a `mult`."
  (mult:untap-all))

(defprotocol Mix
  (admix [_ ch])
  (unmix [_ ch])
  (unmix-all [_])
  (toggle [_ state-map])
  (solo-mode [_ mode]))

(fn mix [out]
  "Creates and returns a mix of one or more input channels which will
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
         thus also not included in the mix)"
  (let [atom {:cs {}
              :solo-mode :mute}
        solo-modes {:mute true :pause true}
        change (chan (sliding-buffer 1))
        changed #(put! change true)
        pick (fn [attr chs]
               (collect [c v (pairs chs)]
                 (when (. attr v)
                   (values c true))))
        calc-state (fn []
                     (let [chs atom.cs
                           mode atom.solo-mode
                           solos (pick :solo chs)
                           pauses (pick :pause chs)]
                       {:solos solos
                        :mutes (pick :mute chs)
                        :reads (doto (if (and (= mode :pause) (next solos))
                                         (icollect [k (pairs solos)] k)
                                         (icollect [k (pairs chs)]
                                           (when (not (. pauses k))
                                             k)))
                                 (table.insert change))}))
        m (reify
           Mux
           (muxch [_] out)
           Mix
           (admix [_ ch] (tset atom :cs ch {}) (changed))
           (unmix [_ ch] (tset atom :cs ch nil) (changed))
           (unmix-all [_] (tset atom :cs {}) (changed))
           (toggle [_ state-map]
                   (tset atom :cs (-merge-with -merge atom.cs state-map))
                   (changed))
           (solo-mode [_ mode]
                      (when (not (. solo-modes mode))
                        (assert false (.. "mode must be one of: "
                                          (table.concat (icollect [k (pairs solo-modes)] k) ", "))))
                      (tset atom :solo-mode mode)
                      (changed)))]
    (go-loop [{: solos : mutes : reads &as state} (calc-state)]
      (let [[v c] (alts! reads)]
        (if (or (= nil v) (= c change))
            (do (when (= nil v)
                  (tset atom :cs c nil))
                (recur (calc-state)))
            (if (or (. solos c)
                    (and (not (next solos)) (not (. mutes c))))
                (when (>! out v)
                  (recur state))
                (recur state)))))
    (doto m (tset :state atom) (tset :st calc-state))))

(fn admix [mix ch]
  "Adds `ch` as an input to the `mix`."
  (mix:admix ch))

(fn unmix [mix ch]
  "Removes `ch` as an input to the `mix`."
  (mix:unmix ch))

(fn unmix-all [mix]
  "Removes all inputs from the `mix`."
  (mix:unmix-all))

(fn toggle [mix state-map]
  "Atomically sets the state(s) of one or more channels in a `mix`.  The
`state-map` is a map of channels -> channel-state-map.  A
channel-state-map is a map of attrs -> boolean, where attr is one or
more of `:mute`, `:pause` or `:solo`.  Any states supplied are merged
with the current state.

Note that channels can be added to a `mix` via `toggle', which can be
used to add channels in a particular (e.g. paused) state."
  (mix:toggle state-map))

(fn solo-mode [mix mode]
  "Sets the solo mode of the `mix`.  `mode` must be one of `:mute` or
`:pause`."
  (mix:solo-mode mode))

(defprotocol Pub
  (sub [_ v ch close?])
  (unsub [_ v ch])
  (unsub-all [_ v]))

(fn pub [ch topic-fn buf-fn]
  "Creates and returns a pub(lication) of the supplied channel `ch`,
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
the source."
  (let [buf-fn (or buf-fn #nil)
        atom {:mults {}}
        ensure-mult (fn [topic]
                      (case (. atom :mults topic)
                        m m
                        nil (let [mults atom.mults
                                  m (mult (chan (buf-fn topic)))]
                              (doto mults (tset topic m))
                              m)))
        p (reify
           Mux
           (muxch [_] ch)

           Pub
           (sub [_ topic ch close?]
                (let [m (ensure-mult topic)]
                  (m:tap ch close?)))
           (unsub [_ topic ch]
                  (case (. atom :mults topic)
                    m (m:untap ch)))
           (unsub-all [_ topic]
                      (if topic
                          (tset atom :mults topic nil)
                          (tset atom :mults {}))))]
    (go-loop []
      (let [val (<! ch)]
        (if (= nil val)
            (each [_ m (pairs atom.mults)]
              (close! (m:muxch)))
            (let [topic (topic-fn val)]
              (case (. atom :mults topic)
                m (when (not (>! (m:muxch) val))
                    (tset atom :mults topic nil)))
              (recur)))))
    p))

(fn sub [pub topic ch ...]
  {:fnl/docstring "Subscribes a channel `ch` to a `topic` of a `pub`.
By default the channel will be closed when the source closes, but can
be determined by the `close?` parameter."
   :fnl/arglist [pub topic ch close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (pub:sub topic ch close?)))

(fn unsub [pub topic ch]
  "Unsubscribes a channel `ch` from a `topic` of a `pub`."
  (pub:unsub topic ch))

(fn unsub-all [pub topic]
  "Unsubscribes all channels from a `pub`, or a `topic` of a `pub`."
  (pub:unsub-all topic))

;;;

(fn map [f chs buf-or-n]
  "Takes a function and a collection of source channels `chs`, and
returns a channel which contains the values produced by applying `f`
to the set of first items taken from each source channel, followed by
applying `f` to the set of second items from each channel, until any
one of the channels is closed, at which point the output channel will
be closed.  The returned channel will be unbuffered by default, or a
`buf-or-n` can be supplied."
  (var dctr nil)
  (let [out (chan buf-or-n)
        cnt (length chs)
        rets {:n cnt}
        dchan (chan 1)
        done (fcollect [i 1 cnt]
               (fn [ret]
                 (tset rets i ret)
                 (set dctr (- dctr 1))
                 (when (= 0 dctr)
                   (put! dchan rets))))]
    (if (= 0 cnt)
        (close! out)
        (go-loop []
          (set dctr cnt)
          (for [i 1 cnt]
            (case (pcall take! (. chs i) (. done i))
              false (set dctr (- dctr 1))))
          (let [rets (<! dchan)]
            (if (faccumulate [res false
                              i 1 rets.n
                              :until res]
                  (= nil (. rets i)))
                (close! out)
                (do (>! out (f ((or _G.unpack table.unpack) rets)))
                    (recur))))))
    out))

(fn merge [chs buf-or-n]
  "Takes a collection of source channels `chs` and returns a channel which
contains all values taken from them.  The returned channel will be
unbuffered by default, or a `buf-or-n` can be supplied.  The channel
will close after all the source channels have closed."
  (let [out (chan buf-or-n)]
    (go-loop [cs chs]
      (if (> (length cs) 0)
          (let [[v c] (alts! cs)]
            (if (= nil v)
                (recur (icollect [_ c* (ipairs cs)]
                         (when (not= c* c) c*)))
                (do (>! out v)
                    (recur cs))))
          (close! out)))
    out))

(fn into [t ch]
  "Returns a channel containing the single (collection) result of the
items taken from the channel `ch` conjoined to the supplied collection
`t`.  `ch` must close before `into` produces a result."
  (reduce #(doto $1 (tset (+ 1 (length $1)) $2)) t ch))

(fn take [n ch buf-or-n]
  "Returns a channel that will return, at most, `n` items from
`ch`.  After n items have been returned, or `ch` has been closed, the
return chanel will close.  The output channel is unbuffered by
default, unless `buf-or-n` is given."
  (let [out (chan buf-or-n)]
    (go (var done false)
        (for [i 0 (- n 1) :until done]
          (case (<! ch)
            v (>! out v)
            nil (set done true)))
        (close! out))
    out))

(comment
 (let [a (to-chan! [1 2 3])
       b (to-chan! [4 5 6])]
   (take! (into [] (merge [a b])) pprint))

 (let [a (chan 1)
       _ (for [i 1 4] (put! a i))
       _ (close! a)
       b (chan 2)
       _ (for [i 5 8] (put! b i))
       _ (close! b)]
   (take! (into [] (merge [a b])) pprint))

 (let [a (chan 2)]
   (go (alts! [[a :a] [a :b] nil]))
   (take! a pprint)
   (take! a pprint))

 (do
   (local a (chan 10))
   (local b (chan 10))
   (put! a :a)
   (put! b :b)
   (go (alts! [[a :c] [b :d] nil]))
   (put! a :e)
   (put! b :f)
   (take! a (partial print :1from-a))
   (take! b (partial print :1from-b))
   (take! a (partial print :2from-a))
   (take! b (partial print :2from-b))
   (take! a (partial print :3from-a))
   (take! b (partial print :3from-b))
   )

 (do
   (local a (chan 10))
   (local b (chan 10))
   (put! a :a)
   (put! b :b)
   (go (pprint (alts! [a b])))
   )

 (let [c (chan)]
   (put! c -2)
   (put! c -1)
   (put! c 0)
   (pipe (to-chan! [1 2 3 4 5]) c)
   (take! (into [] c) pprint))

 (fn mapper [f]
   (fn [rf]
     (fn [...]
       (print :mapper ...)
       (case (select :# ...)
         0 (rf)
         1 (rf ...)
         _ (rf ... (f (select 2 ...)))))))

 (fn filterer [f]
   (fn [rf]
     (fn [...]
       (print :filterer ...)
       (case (select :# ...)
         0 (rf)
         1 (rf ...)
         _ (let [(result val) ...]
             (if (f val)
                 (rf result val)
                 result))))))

 (fn comp [f g]
   #(f (g $...)))

 (let [c (chan 1 (mapper #(* $ $)))]
   (pipe (to-chan! (fcollect [i 1 10] i)) c)
   (take! (into [] c) pprint))

 (let [c (chan 1 (filterer #(= 0 (% $ 2))))]
   (pipe (to-chan! (fcollect [i 1 10] i)) c)
   (take! (into [] c) pprint))

 (let [c (chan 1 (comp (filterer #(= 0 (% $ 2)))
                       (mapper #(* $ $))))]
   (pipe (to-chan! (fcollect [i 1 10] i)) c)
   (take! (into [] c) pprint))

 (let [c (to-chan! [1 2 3 4 5])
       out (chan)]
   (pipeline 10 out (comp (filterer #(= 0 (% $ 2)))
                          (mapper #(* $ $))) c)
   (take! (into [] out) pprint))

 (macro time [body]
   `(let [s# (-time)
          pack# #(doto [$...] (tset :n (select :# $...)))
          res# (pack# ,body)]
      (print "Elapsed: " (* 1000 (- (-time) s#)) " ms")
      ((or _G.unpack table.unpack) res# 1 res#.n)))

 (time
  (do
    (fn af-inc [v c]
      (go (print :doing: v)
          (<! (timeout 1700))
          (>! c (+ v 1))
          (close! c)
          (print :done: v)))
    (local data (to-chan! [1 2 3 4 5 6 7 8 9 10]))
    (local results (chan))
    (pipeline-async 10 results af-inc data true)
    (pprint (<!! (into [] results)))))

 (time
  (let [c (chan 1)]
    (>!! c 10)
    (pprint :put1 c.buf.buf c.puts c.takes)
    (go (<! (timeout 3000)) (print :remove (<! c)))
    (>!! c 20)
    (pprint :put2 c.buf.buf c.puts c.takes)
    (pprint :remove (<!! c))))

 (do
   (local c (chan))
   (local m (mult c))
   (local c1 (chan))
   (tap m c1)
   (local c2 (chan))
   (tap m c2)
   (local c3 (chan))
   (tap m c3)
   (put! c 42)
   (take! c1 (partial print 1 :c1))
   (take! c2 (partial print 1 :c2))
   (take! c3 (partial print 1 :c3))
   (untap m c1)
   (put! c 27)
   (take! c1 (partial print 2 :c1))
   (take! c2 (partial print 2 :c2))
   (take! c3 (partial print 2 :c3))
   (untap-all m)
   (put! c 72)
   (take! c1 (partial print 3 :c1))
   (take! c2 (partial print 3 :c2))
   (take! c3 (partial print 3 :c3))
   )

 (do (local c (chan 1))
     (go (let [m (mix c)
               c1 (chan 1)
               c2 (chan 1)
               c3 (chan 1)]
           (admix m c1)
           (admix m c2)
           (admix m c3)
           (put! c1 :a)
           (put! c2 :b)
           (put! c3 :c)
           (unmix m c2)
           (put! c1 :d)
           (put! c2 :e)
           (put! c3 :f)
           (unmix-all m)
           (put! c1 :g)
           (put! c2 :h)
           (put! c3 :i)))
     (take! c pprint)
     (take! c pprint)
     (take! c pprint)
     )

 (do
   (local c (chan))
   (local sub-c (pub c #(. $ :route)))
   (local cx (chan))
   (sub sub-c :up-stream cx)
   (local cy (chan))
   (sub sub-c :down-stream cy)
   (take! cx pprint)
   (take! cy pprint)
   (put! c {:route :up-stream :data 123})
   (put! c {:route :down-stream :data 123})
   )
 )

(-register-hook -advance-timeouts)

{: buffer
 : dropping-buffer
 : sliding-buffer
 : promise-buffer
 : unblocking-buffer?
 : chan
 : promise-chan
 : take!
 : <!!
 : <!
 : timeout
 : put!
 : >!!
 : >!
 : close!
 :go go*
 : alts!
 : offer!
 : poll!
 : pipe
 : pipeline-async
 : pipeline
 : reduce
 : transduce
 : split
 : onto-chan!
 : to-chan!
 : mult
 : tap
 : untap
 : untap-all
 : mix
 : admix
 : unmix
 : unmix-all
 : toggle
 : solo-mode
 : pub
 : sub
 : unsub
 : unsub-all
 : map
 : merge
 : into
 : take
 :buffers
 {: FixedBuffer
  : SlidingBuffer
  : DroppingBuffer
  : PromiseBuffer}}
