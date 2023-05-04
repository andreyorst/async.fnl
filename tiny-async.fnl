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

(local FixedBuffer
  {:type -buf
   :full? (fn [{:buf buffer : size}] (= (length buffer) size))
   :empty? (fn [{:buf buffer}] (= 0 (length buffer)))
   :length (fn [{:buf buffer}] (length buffer))
   :put (fn [{:buf buffer : size} val]
          (assert (not= val nil) "value must not be nil")
          (let [len (length buffer)]
            (when (< len size)
              (tset buffer (+ 1 len) val)
              true)))
   :take (fn [{:buf buffer}]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local DroppingBuffer
  {:type -buf
   :full? #false
   :empty? (fn [{:buf buffer}] (= 0 (length buffer)))
   :length (fn [{:buf buffer}] (length buffer))
   :put (fn [{:buf buffer : size} val]
          (assert (not= val nil) "value must not be nil")
          (when (< (length buffer) size)
            (tset buffer (+ 1 (length buffer)) val))
          true)
   :take (fn [{:buf buffer}]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local SlidingBuffer
  {:type -buf
   :full? #false
   :empty? (fn [{:buf buffer}] (= 0 (length buffer)))
   :length (fn [{:buf buffer}] (length buffer))
   :put (fn [{:buf buffer : size} val]
          (assert (not= val nil) "value must not be nil")
          (tset buffer (+ 1 (length buffer)) val)
          (when (< size (length buffer))
            (table.remove buffer 1))
          true)
   :take (fn [{:buf buffer}]
           (when (> (length buffer) 0)
             (table.remove buffer 1)))})

(local PromiseBuffer
  {:type -buf
   :full? (fn [{:buf [val]}] (not= nil val))
   :empty? (fn [{:buf buffer}] (= 0 (length buffer)))
   :length (fn [{:buf buffer}] (length buffer))
   :put (fn [{:buf buffer} val]
          (assert (not= val nil) "value must not be nil")
          (when (= 0 (length buffer))
            (tset buffer 1 val))
          true)
   :take (fn [{:buf [val]}] val)})

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

(fn buffer [size]
  "Create a buffer of set `size`.

When the buffer is full, returns `false'.  Taking from the buffer must
return `nil', if the buffer is empty."
  (-buffer size FixedBuffer))

(fn dropping-buffer [size]
  "Create a dropping buffer of set `size`.

When the buffer is full puts will succeed, but the value will be
dropped."
  (-buffer size DroppingBuffer))

(fn sliding-buffer [size]
  "Create a sliding buffer of set `size`.

When the buffer is full puts will succeed, but the oldest value in the
buffer will be dropped."
  (-buffer size SlidingBuffer))

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

;; (-register-hook -advance-timeouts)

(fn -make-thunk [thunk active-fn name]
  (->> {:__name name
        :__fennelview
        #(.. "#<" (: (tostring $) :gsub "table:" (.. name ":")) ">")}
       (setmetatable {:thunk thunk :active? active-fn})))

(fn -try-buffer [chan val callback]
  (case chan.buf
    (where buf (not (buf:full?)))
    (do (case chan.xform
          xform (xform buf val)
          nil (buf:put val))
        (when callback (callback true))
        true)))

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
                       (if (take.active?)
                           (do (case (coroutine.resume
                                      take.thunk
                                      (if buffered? (chan.buf:take) val))
                                 (false msg) (chan.err-handler msg))
                               (callback true)
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
                       (where {: buf : puts} (not (buf:empty?)))
                       (let [val (buf:take)
                             len (buf:length)]
                         ((fn loop []
                            (case (table.remove puts 1)
                              put (let [[put val*] put]
                                    (if (put.active?)
                                        (let [_ (-try-buffer chan val*)
                                              len* (buf:length)]
                                            (case (coroutine.resume put.thunk)
                                              (false msg) (chan.err-handler msg))
                                            (when (= len len*)
                                              (loop)))
                                        (loop))))))
                         (callback val)
                         val)
                       (where {: puts} (next puts))
                       (let [[put val] (table.remove puts 1)]
                         (if (put.active?)
                             (do (callback val)
                                 (case (coroutine.resume put.thunk)
                                   (false msg) (chan.err-handler msg))
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
             (when (not enqueue?)
               res)))
   :close (fn [chan]
            (when (not chan.closed)
              (set chan.closed true)
              (while (> (length chan.takes) 0)
                (let [take (table.remove chan.takes 1)]
                  (when (take.active?)
                    (case (coroutine.resume take.thunk)
                      (false msg) (chan.err-handler msg)))))))})

(fn -err-handler [mesg]
  (io.stderr:write (tostring mesg) "\n")
  nil)

(fn chan [?buffer-or-size ?xform ?err-handler]
  "Create a chanel with optional buffer."
  (let [buffer (match ?buffer-or-size
                 {:type -buf} ?buffer-or-size
                 0 nil
                 size (buffer size))
        xform (when ?xform
                (assert (not= nil buffer) "buffer must be supplied when transducer is")
                (?xform (fn [...]
                          (case (values (select :# ...) ...)
                            (1 buffer) buffer
                            (2 buffer val) (: buffer :put val)))))]
    (setmetatable
     {:puts []
      :takes []
      :buf buffer
      :xform xform
      :err-handler (or ?err-handler -err-handler)}
     {:__index Channel
      :__name "channel"
      :__fennelview
      #(.. "#<" (: (tostring $) :gsub "table:" "channel:") ">")})))

(fn promise-chan [?xform ?err-handler]
  (chan (promise-buffer) ?xform ?err-handler))

(fn timeout [seconds]
  "Create a channel that will be closed after specified amount of
`seconds`.  Note, this requires `debug.sethook` to be available."
  (assert (and gethook sethook) "Can't advance timers - debug.sethook unavailable")
  (let [t (+ (-time) (- seconds 1))]
    (or (. -timeouts t)
        (let [c (chan)]
          (tset -timeouts t c)
          c))))

(fn -make-callback [f active-f]
  (->> {:__call (fn [self ...] (when (active-f) ((or f #nil) ...)))}
       (setmetatable {:active? active-f})))

(fn take! [channel callback]
  "Take value off the `channel`.
If the channel has a value in a buffer or a pending put, returns
immediatelly.  When called inside the `thread`, parks registers a
pending take on the channel and parks the thread.  If the channel is
closed returns nil.  When called in the main thread assigns a
`callback` as pending take."
  (assert (-chan? channel) "expected a channel as first argument")
  (assert (not (and (-main-thread?) (= nil callback)))
          "expected a callback")
  (channel:take
   (-make-callback callback #true)
   (and callback true)))

(fn put! [channel value callback]
  "Put the `value` onto a `channel`.
If the channel has a buffer, puts the value immediatelly, and returns
`true`.  When called inside the `thread`, if the buffer is full or of
size `0` registers a pending put, and parks the thread.  If there's a
pending take, passes a value to the take thread and continues.
Otherwise returns `nil`."
  (assert (-chan? channel) "expected a channel as first argument")
  (channel:put value (-make-callback callback #true)))

(fn close! [chan]
  (assert (-chan? chan) "expected a channel")
  (chan:close))

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
                         #(let [res [$ c]]
                            (set state.active? false)
                            (put! res-ch res)
                            (close! res-ch))
                         #state.active?)
                        true)
          c (c:take (-make-callback
                     #(let [res [$ c]]
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

(fn offer! [channel value]
  (assert (-chan? channel) "expected a channel as first argument")
  (channel:put value (-make-callback #nil #false)))

(fn poll! [channel]
  (assert (-chan? channel) "expected a channel")
  (channel:take
   (-make-callback #nil #false)
   false))

;;; Operations

(fn pipe [from to ...]
  {:fnl/docstring "Pipe all values from `from` to `to`.  Once `from` is closed,
`to` is also closed, unless `close?` is false."
   :fnl/arglist [from to close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (go (fn loop []
          (let [val (take! from)]
            (if (= nil val)
                (when close? (close! to))
                (loop (put! to val))))))))

(fn -pipeline [n to xf from close? err-handler kind]
  (let [jobs (chan n)
        results (chan n)
        finishes (and (= kind :async) (chan n))
        process (fn [job]
                  (case job
                    nil (do (close! results) nil)
                    [v p] (let [res (chan 1 xf err-handler)]
                            (go #(do
                                   (put! res v)
                                   (close! res)))
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
    (for [i 1 n]
      (case kind
        :compute (go (fn loop []
                       (let [job (take! jobs)]
                         (when (process job)
                           (loop)))))
        :async (go (fn loop []
                     (let [job (take! jobs)]
                       (when (async job)
                         (take! finishes)
                         (loop)))))))
    (go (fn loop []
          (match (take! from)
            nil (close! jobs)
            v (let [p (chan 1)]
                (put! jobs [v p])
                (put! results p)
                (loop)))))
    (go (fn loop []
          (case (take! results)
            nil (when (not= close? false)
                  (close! to))
            p (case (take! p)
                res (do ((fn loop* []
                           (case (take! res)
                             val (do (put! to val)
                                     (loop*)))))
                        (when finishes
                          (put! finishes :done))
                        (loop))))))))

(fn pipeline-async [n to af from close?]
  (-pipeline n to af from close? nil :async))

(fn pipeline [n to xf from close? ex-handler]
  (-pipeline n to xf from close? ex-handler :compute))

(fn reduce [f init ch]
  (go #((fn loop [ret]
          (let [v (take! ch)]
            (if (= nil v) ret
                (loop (f ret v)))))
        init)))

(fn transduce [xform f init ch]
  (let [f (xform f)]
    (go #(let [ret (take! (reduce f init ch))]
           (f ret)))))

(fn split [p ch ?t-buf-or-n ?f-buf-or-n]
  (let [tc (chan ?t-buf-or-n)
        fc (chan ?f-buf-or-n)]
    (go (fn loop []
          (let [v (take! ch)]
            (if (= nil v)
                (do (close! tc) (close! fc))
                (when (put! (if (p v) tc fc) v)
                  (loop))))))
    [tc fc]))

(fn onto-chan! [chan t ...]
  {:fnl/docstring "Puts the contents of coll into the supplied channel.
By default the channel will be closed after the items are copied, but
can be determined by the close? parameter.  Returns a channel which
will close after the items are copied."
   :fnl/arglist [chan t close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (go #(do (each [_ v (ipairs t)]
               (put! chan v))
             (when close? (close! chan))
             chan))))

(fn -bounded-length [bound t]
  (math.min bound (length t)))

(fn to-chan! [t]
  (let [ch (chan (-bounded-length 100 t))]
    (onto-chan! ch t)
    ch))

;;; Mux/Mix/Tap

(local Mux {:muxch* (fn [_])})

(local Mult
  {:tap (fn [m ch close?])
   :untap (fn [m ch] nil)
   :untap-all (fn [m])})

(fn mult [ch])

(fn tap [mult ch close?]
  "Copies the mult source onto the supplied channel.
  By default the channel will be closed when the source closes,
  but can be determined by the close? parameter."
  (mult:tap ch close?) ch)

(fn untap [mult ch]
  "Disconnects a target channel from a mult"
  (mult:untap ch))

(fn untap-all [mult]
  "Disconnects all target channels from a mult"
  (mult:untap-all))

(local Mix
  {:admix (fn [m ch])
   :unmix (fn [m ch])
   :unmix-all (fn [m])
   :toggle (fn [m state-map])
   :solo-mode (fn [m mode])})

(fn ioc-alts! [state cont-block ports & {:as opts}])

(fn mix [out]
  "Creates and returns a mix of one or more input channels which will
be put on the supplied out channel. Input sources can be added to the
mix with 'admix', and removed with 'unmix'. A mix supports soloing,
muting and pausing multiple inputs atomically using 'toggle', and can
solo using either muting or pausing as determined by 'solo-mode'.

Each channel can have zero or more boolean modes set via 'toggle':

:solo - when true, only this (ond other soloed) channel(s) will appear
        in the mix output channel. :mute and :pause states of soloed
        channels are ignored. If solo-mode is :mute, non-soloed
        channels are muted, if :pause, non-soloed channels are paused.
:mute - muted channels will have their contents consumed but not
        included in the mix
:pause - paused channels will not have their contents consumed (and
         thus also not included in the mix)")

(fn admix [mix ch]
  "Adds ch as an input to the mix"
  (mix:admix ch))

(fn unmix [mix ch]
  "Removes ch as an input to the mix"
  (mix:unmix ch))

(fn unmix-all [mix]
  "removes all inputs from the mix"
  (mix:unmix-all))

(fn toggle [mix state-map]
  "Atomically sets the state(s) of one or more channels in a mix. The
  state map is a map of channels -> channel-state-map. A
  channel-state-map is a map of attrs -> boolean, where attr is one or
  more of :mute, :pause or :solo. Any states supplied are merged with
  the current state.
  Note that channels can be added to a mix via toggle, which can be
  used to add channels in a particular (e.g. paused) state."
  (mix:toggle state-map))

(fn solo-mode [mix mode]
  "Sets the solo mode of the mix. mode must be one of :mute or :pause"
  (mix:solo-mode mode))

(local Pub
  {:sub (fn [p v ch close?])
   :unsub (fn [p v ch])
   :unsub-all (fn [p v])})

(fn pub [ch topic-fn buf-fn])

(fn sub [p topic ch close?]
  "Subscribes a channel to a topic of a pub.
  By default the channel will be closed when the source closes,
  but can be determined by the close? parameter."
  (p:sub topic ch close?))

(fn unsub [p topic ch]
  "Unsubscribes a channel from a topic of a pub"
  (p:unsub topic ch))

(fn unsub-all [p topic]
  "Unsubscribes all channels from a pub, or a topic of a pub"
  (p:unsub-all topic))

;;;

(fn map [f chs ?buf-or-n]
  (var dctr nil)
  (let [out (chan ?buf-or-n)
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
        (go (fn loop []
              (set dctr cnt)
              (for [i 1 cnt]
                (case (pcall take! (. chs i) (. done i))
                  false (set dctr (- dctr 1))))
              (let [rets (take! dchan)]
                (if (faccumulate [res false
                                  i 1 rets.n
                                  :until res]
                      (= nil (. rets i)))
                    (close! out)
                    (do (put! out (f ((or _G.unpack table.unpack) rets)))
                        (loop)))))))
    out))

(fn merge [chs ?buf-or-n]
  (let [out (chan ?buf-or-n)]
    (go #((fn loop [cs]
            (if (> (length cs) 0)
                (let [[v c &as r] (alts! cs)]
                  (if (= nil v)
                      (loop (icollect [_ c* (ipairs cs)]
                              (when (not= c* c) c*)))
                      (do (put! out v)
                          (loop cs))))
                (close! out)))
          chs))
    out))

(fn into [t ch]
  (reduce #(doto $1 (tset (+ 1 (length $1)) $2)) t ch))

(fn take [n ch ?buf-or-n]
  (let [out (chan ?buf-or-n)]
    (go #(do (var done false)
             (for [i 0 (- n 1) :until done]
               (case (take! ch)
                 v (put! out v)
                 nil (set done true)))
             (close! out)))
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

 (fn delayed-inc [v c]
   (go #(do (print :doing: v)
            ;; (take! (timeout 1))
            (put! c (+ v 1))
            (close! c)
            (print :done: v))))
 (local data (to-chan! [1 2 3 4 5 6 7 8 9 10])) (local results (chan))
 (pipeline-async 3 results delayed-inc data true)
 (take! (into [] results) pprint)
 (fn mapper [f]
   (fn [rf]
     (fn [...]
       (case (select :# ...)
         0 (rf)
         1 (rf ...)
         _ (rf ... (f (select 2 ...)))))))
 (let [c (chan 1 (mapper #(* $ $)))]
   (pipe (to-chan! (fcollect [i 1 10] i)) c)
   (take! (into [] c) pprint))
 (fn filterer [f]
   (fn [rf]
     (fn [...]
       (case (select :# ...)
         0 (rf)
         1 (rf ...)
         _ (let [(result val) ...]
             (if (f val)
                 (rf result val)
                 result))))))
 (let [c (chan 1 (filterer #(= 0 (% $ 2))))]
   (pipe (to-chan! (fcollect [i 1 10] i)) c)
   (take! (into [] c) pprint))
 )

{: buffer
 : dropping-buffer
 : sliding-buffer
 : promise-buffer
 : unblocking-buffer?
 : chan
 : promise-chan
 : timeout
 : take!
 : put!
 : close!
 : go
 : alts!
 : offer!
 : poll!
 : pipe
 : pipeline-async
 : pipeline
 : onto-chan!
 : to-chan!
 : reduce
 : transduce
 : split
 : map
 : merge
 : into
 : take
 :buffers
 {: FixedBuffer
  : SlidingBuffer
  : DroppingBuffer
  : PromiseBuffer}}
