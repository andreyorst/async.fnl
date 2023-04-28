(comment
 "MIT License

Copyright (c) 2023 Andrey Listopadov

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the “Software”), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.")

(local -lib-name
  (or ... "tiny-async"))

(local {: gethook : sethook}
  (case _G.debug
    {: gethook : sethook} {: gethook : sethook}
    _ (do (io.stderr:write
           "WARNING: debug library is unawailable. "
           -lib-name " uses debug.sethook to advance timers. "
           "Time-related features are disabled.\n")
          {})))

(fn -main-thread? []
  "Check if current thread is a main one and not a coroutine."
  (case (coroutine.running)
    nil true
    (_ true) true
    _ false))

;;; Buffers

(local -buf {})

(local Buffer
  {:type -buf
   :full? (fn [buffer] (= (length buffer) buffer.size))
   :empty? (fn [buffer] (= 0 (length buffer)))
   :put (fn [buffer val]
          (assert (not= val nil) "value must not be nil")
          (let [len (length buffer)]
            (when (< len buffer.size)
              (tset buffer (+ 1 len) val)
              true)))
   :take (fn [buffer]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local DroppingBuffer
  {:type -buf
   :full? #false
   :empty? (fn [buffer] (= 0 (length buffer)))
   :put (fn [buffer val]
          (assert (not= val nil) "value must not be nil")
          (when (< (length buffer) buffer.size)
            (tset buffer (+ 1 (length buffer)) val))
          true)
   :take (fn [buffer]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local SlidingBuffer
  {:type -buf
   :full? #false
   :empty? (fn [buffer] (= 0 (length buffer)))
   :put (fn [buffer val]
          (assert (not= val nil) "value must not be nil")
          (tset buffer (+ 1 (length buffer)) val)
          (when (< buffer.size (length buffer))
            (table.remove buffer 1))
          true)
   :take (fn [buffer]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local PromiseBuffer
  {:type -buf
   :full? (fn [[val]] (not= nil val))
   :empty? (fn [buffer] (= 0 (length buffer)))
   :put (fn [buffer val]
          (assert (not= val nil) "value must not be nil")
          (when (= 0 (length buffer))
            (tset buffer 1 val))
          true)
   :take (fn [[val]] val)})

(fn -buffer [size buffer-type]
  (and size (assert (= :number (type size)) (.. "size must be a number: " (tostring size))))
  (assert (not (: (tostring size) :match "%.")) "size must be integer")
  (setmetatable
   {:size size}
   {:__index buffer-type
    :__name "buffer"
    :__fennelview #(.. "#<" (: (tostring $) :gsub "table:" "buffer:") ">")}))

(fn buffer [size]
  "Create a buffer of set `size`.

When the buffer is full, returns `false'.  Taking from the buffer must
return `nil', if the buffer is empty."
  (-buffer size Buffer))

(fn sliding-buffer [size]
  "Create a sliding buffer of set `size`.

When the buffer is full puts will succeed, but the oldest value in the
buffer will be dropped."
  (-buffer size SlidingBuffer))

(fn dropping-buffer [size]
  "Create a dropping buffer of set `size`.

When the buffer is full puts will succeed, but the value will be
dropped."
  (-buffer size DroppingBuffer))

(fn promise-buffer []
  "Create a promise buffer.

When the buffer receives a value all other values are dropped.  Taking
a value from the buffer doesn't remove it from the buffer."
  (-buffer 1 PromiseBuffer))

(fn -buffer? [obj]
  (match obj
    {:type -buf} true
    _ false))

(fn unblocking-buffer? [obj]
  "Return true if `obj` is a buffer that never blocks on puts."
  (match (and (-buffer? obj)
              (. (getmetatable obj) :__index))
    SlidingBuffer true
    DroppingBuffer true
    PromiseBuffer true
    _ false))

;;; Channels

(local -chan {})
(local -timeouts {})
(local -time os.time)
(local -difftime
  (or os.difftime #(- $1 $2)))

(fn -chan? [obj]
  (match obj {:type -chan} true _ false))

(fn -advance-timeouts []
  "Close any timeout channels whose closing time is less than or equal
to current time."
  (when (next -timeouts)
    (let [to-remove (icollect [t ch (pairs -timeouts)]
                      (when (> 0 (-difftime t (-time)))
                        (ch:close)
                        t))]
      (each [_ t (ipairs to-remove)]
        (tset -timeouts t nil)))))

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

(-register-hook -advance-timeouts)

(fn -make-thunk [thunk active-fn name]
  (->> {:__name name
        :__fennelview #(.. "#<" (: (tostring $) :gsub "table:" (.. name ":")) ">")}
       (setmetatable {:thunk thunk :active? active-fn})))

(local Channel
  {:type -chan
   :put (fn loop [chan val callback enqueue?]
          (assert (not= val nil) "val must not be nil")
          (if chan.closed
              false
              (when (callback.active?)
                (case chan
                  (where {: takes} (next takes))
                  (let [take (table.remove takes 1)]
                    (if (take.active?)
                        (do (case (coroutine.resume take.thunk val)
                              (false msg) (error msg))
                            (callback))
                        (loop chan val callback enqueue?)))
                  (where {: buf} (not (buf:full?)))
                  (do
                    (buf:put val)
                    (callback))
                  (where {: puts} (< (length puts) 1024))
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
                        (callback)))
                  _ (error "too many pending puts"))
                true)))
   :take (fn loop [chan callback enqueue?]
           (assert (not= nil callback) "expected a callback")
           (let [res (when (callback.active?)
                       (match chan
                         (where {: buf : puts} (not (buf:empty?)))
                         (let [val (buf:take)]
                           ((fn loop []
                              (case (table.remove puts 1)
                                put (let [[put val*] put]
                                      (if (put.active?)
                                          (do (buf:put val*)
                                              (case (coroutine.resume put.thunk)
                                                (false msg) (error msg)))
                                          (loop))))))
                           (callback val)
                           val)
                         (where {: puts} (next puts))
                         (let [[put val] (table.remove puts 1)]
                           (if (put.active?)
                               (do (callback val)
                                   (case (coroutine.resume put.thunk)
                                     (false msg) (error msg))
                                   val)
                               (loop chan callback enqueue?)))
                         (where {: takes &as chan} (< (length takes) 1024))
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
                         _ (error "too many pending takes")))]
             (when (not (or (-main-thread?) enqueue?))
               res)))
   :close (fn [chan]
            (when (not chan.closed)
              (set chan.closed true)
              (while (> (length chan.takes) 0)
                (let [take (table.remove chan.takes 1)]
                  (when (take.active?)
                    (case (coroutine.resume take.thunk)
                      (false msg) (error msg)))))))})

(fn -make-callback [f active-f]
  (->> {:__call (fn [self ...] (when (active-f) ((or f #nil) ...)))}
       (setmetatable {:active? active-f})))

(fn put! [channel value callback]
  "Put the `value` onto a `channel`.
If the channel has a buffer, puts the value immediatelly, and returns
`true`.  When called inside the `thread`, if the buffer is full or of
size `0` registers a pending put, and parks the thread.  If there's a
pending take, passes a value to the take thread and continues.
Otherwise returns `nil`."
  (assert (-chan? channel) "expected a channel as first argument")
  (channel:put value (-make-callback callback #true)))

(fn take! [channel callback]
  "Take value off the `channel`.
If the channel has a value in a buffer or a pending put, returns
immediatelly.  When called inside the `thread`, parks registers a
pending take on the channel and parks the thread.  If the channel is
closed returns nil.  When called in the main thread assigns a
`callback` as pending take."
  (assert (-chan? channel) "expected a channel as first argument")
  (channel:take
   (-make-callback callback #true)
   (and callback true)))

(fn close! [chan]
  (assert (-chan? chan) "expected a channel")
  (chan:close))

(fn chan [?bufer-or-size]
  "Create a chanel with optional buffer."
  (setmetatable
   {:puts []
    :takes []
    :buf (match ?bufer-or-size
           {:type -buf} ?bufer-or-size
           size (buffer size))}
   {:__index Channel
    :__name "channel"
    :__fennelview #(.. "#<" (: (tostring $) :gsub "table:" "channel:") ">")}))

(fn timeout [seconds]
  "Create a channel that will be closed after specified amount of
`seconds`.  Note, this requires `debug.sethook` to be available."
  (assert (and gethook sethook) "Can't advance timers - debug.sethook unavailable")
  (let [t (+ (-time) (- seconds 1))]
    (or (. -timeouts t)
        (let [c (chan)]
          (tset -timeouts t c)
          c))))

(fn go [thunk]
  "Run `thunk` asynchronously.
Returns a channel, that eventually contains result of the execution."
  (let [c (chan 1)]
    (case (-> (fn []
                (case (thunk)
                  val (put! c val))
                (close! c))
              coroutine.create
              coroutine.resume)
      (false msg) (error msg))
    c))

;;; Operations

(fn -random-array [n]
  (let [ids (fcollect [i 1 n] i)]
    (for [i n 2 -1]
      (let [j (math.random i)
            ti (. ids i)]
        (tset ids i (. ids j))
        (tset ids j ti)))
    ids))

(fn alts! [channels opts]
  (assert (not (-main-thread?)) "called alts! on the main thread")
  (let [n (length channels)
        ids (-random-array n)
        res-ch (chan (promise-buffer))
        state {:active? true}]
    (for [i 1 n]
      (let [id (if (and opts opts.priority) i (. ids i))]
        (case (. channels id)
          [c ?v] (c:put ?v
                        (-make-callback
                         #(let [res [c $]]
                            (set state.active? false)
                            (put! res-ch res)
                            (close! res-ch))
                         #state.active?)
                        true)
          c (c:take (-make-callback
                     #(let [res [c $]]
                        (set state.active? false)
                        (put! res-ch res)
                        (close! res-ch))
                     #state.active?)
                    true))))
    (if (and state.active?
             opts opts.default)
        (do (set state.active? false)
            [:default opts.default])
        (take! res-ch))))

(fn pipe [to from keep]
  "Pipe all values from `from` to `to`.  Once `from` is closed,
`to` is also closed, unless `keep` is true."
  (go (fn loop []
        (let [val (take! from)]
          (if (= nil val)
              (when (not keep) (close! to))
              (loop (put! to val)))))))

(fn -bounded-length [bound t]
  (math.min bound (length t)))

(fn onto-chan! [chan t keep?]
  (go #(do (each [_ v (ipairs t)]
             (put! chan v))
           (when (not keep?) (close! chan))
           chan)))

(fn to-chan! [t]
  (let [ch (chan (-bounded-length 100 t))]
    (onto-chan! ch t)
    ch))

(fn merge [chs buf-or-n]
  "Takes a collection of source channels and returns a channel which
  contains all values taken from them. The returned channel will be
  unbuffered by default, or a buf-or-n can be supplied. The channel
  will close after all the source channels have closed."
  (let [out (chan buf-or-n)]
    (go #((fn loop [cs]
            (if (> (length cs) 0)
                (let [[c v] (alts! cs)]
                  (if (= nil v)
                      (loop (icollect [_ c* (ipairs cs)]
                              (when (not= c* c) c*)))
                      (do (put! out v)
                          (loop cs))))
                (close! out)))
          chs))
    out))

(fn reduce [f init ch]
  (go #((fn loop [ret]
          (let [v (take! ch)]
            (if (= nil v) ret
                (loop (f ret v)))))
        init)))

(fn into [t ch]
  (reduce #(doto $1 (tset (+ 1 (length $1)) $2)) t ch))

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

 (let [a (chan)]
   (go #(alts! [[a :a] [a :b] nil]))
   (take! a pprint)
   (pprint a.puts)
   (take! a pprint)
   (pprint a.puts))

 (local a (chan 1))
 (local b (chan 1))
 (put! a :c)
 (put! b :d)
 (go #(alts! [[a :a] [b :b] nil]))
 (put! a :e)
 (put! b :f)
 (pprint {:a a.puts :b b.puts})
 (take! a print)
 (take! b print)

 (let [c (chan)]
   (put! c 0)
   (pipe c (to-chan! [1 2 3 4 5]))
   (take! (into [] c) pprint))
 )

{: go
 : take!
 : put!
 : chan
 : close!
 : buffer
 : sliding-buffer
 : dropping-buffer
 : promise-buffer
 : unblocking-buffer?
 : timeout
 : alts!
 : pipe
 : to-chan!
 : onto-chan!
 : merge
 : into
 :buffers
 {: Buffer
  : SlidingBuffer
  : DroppingBuffer
  : PromiseBuffer}}
