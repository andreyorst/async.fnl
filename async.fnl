(comment
 "Copyright (c) 2023 Andrey Listopadov and contributors. All rights reserved.
The use and distribution terms for this software are covered by the
Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
which can be found in the file epl-v10.html at the root of this distribution.
By using this software in any fashion, you are agreeing to be bound by
the terms of this license.
You must not remove this notice, or any other, from this software.")

;;; Helpers

(local -lib-name
  (or ... "async"))

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
  (let [res {}]
    (collect [k v (pairs t1) :into res]
      k v)
    (collect [k v (pairs t2) :into res]
      k v)))

(fn -merge-with [f t1 t2]
  (let [res (collect [k v (pairs t1)] k v)]
    (collect [k v (pairs t2) :into res]
      (case (. res k)
	e (values k (f e v))
	nil (values k v)))))

(fn -make-callback [f active-f]
  (->> {:__call (fn [_ ...] (when (active-f) ((or f #nil) ...)))}
       (setmetatable {:active? active-f})))

(local -nop (-make-callback #nil #true))

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
  "Returns a fixed buffer of size n. When full, puts will block/park."
  (-buffer size FixedBuffer))

(fn dropping-buffer [size]
  "Returns a buffer of size n. When full, puts will complete but
val will be dropped (no transfer)."
  (-buffer size DroppingBuffer))

(fn sliding-buffer [size]
  "Returns a buffer of size n. When full, puts will complete, and be
buffered, but oldest elements in buffer will be dropped (not
transferred)."
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
  "Returns true if a channel created with buff will never block. That is
to say, puts into this buffer will never cause the buffer to be full."
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
             (when (not enqueue?)
               res)))
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

(fn chan [?buffer-or-size ?xform ?err-handler]
  "Creates a channel with an optional buffer, an optional
transducer, and an optional error handler.  If buffer-or-size is a
number, will create and use a fixed buffer of that size. If a
transducer is supplied a buffer must be specified. err-handler must be
a fn of one argument - if an exception occurs during transformation it
will be called with the thrown value as an argument, and any non-nil
return value will be placed in the channel."
  (let [buffer (match ?buffer-or-size
                 {:type -buf} ?buffer-or-size
                 0 nil
                 size (buffer size))
        xform (when ?xform
                (assert (not= nil buffer) "buffer must be supplied when transducer is")
                (?xform (fn [...]
                          (case (values (select :# ...) ...)
                            (1 buffer) buffer
                            (2 buffer val) (: buffer :put val)))))
        err-handler (or ?err-handler -err-handler)]
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

(fn pipeline-async [n to af from ...]
  {:fnl/docstring nil
   :fnl/arglist [n to af from close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (-pipeline n to af from close? nil :async)))

(fn pipeline [n to xf from ...]
  {:fnl/docstring nil
   :fnl/arglist [n to af from close? err-handler]}
  (let [(err-handler close?) (if (= (select :# ...) 0) true ...)]
    (-pipeline n to xf from close? err-handler :compute)))

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

;;; Mult, Mix, Pub

(defprotocol Mux
  (muxch [_]))

(defprotocol Mult
  (tap [_ ch close?])
  (untap [_ ch])
  (untap-all [_]))

(fn mult [ch]
  "Creates and returns a mult(iple) of the supplied channel. Channels
containing copies of the channel can be created with 'tap', and
detached with 'untap'.

Each item is distributed to all taps in parallel and synchronously,
i.e. each tap must accept before the next item is distributed. Use
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
    (go (fn loop []
          (let [val (take! ch)]
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
                    (take! dchan))
                  (loop))))))
    m))

(fn tap [mult ch ...]
  {:fnl/docstring "Copies the mult source onto the supplied channel.
By default the channel will be closed when the source closes,
but can be determined by the close? parameter."
   :fnl/arglist [mult ch close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (mult:tap ch close?) ch))

(fn untap [mult ch]
  "Disconnects a target channel from a mult"
  (mult:untap ch))

(fn untap-all [mult]
  "Disconnects all target channels from a mult"
  (mult:untap-all))

(defprotocol Mix
  (admix [_ ch])
  (unmix [_ ch])
  (unmix-all [_])
  (toggle [_ state-map])
  (solo-mode [_ mode]))

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
         thus also not included in the mix)"
  (let [atom {:cs {}
              :solo-mode :mute} ;;ch->attrs-map
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
    (go #((fn loop [{: solos : mutes : reads &as state}]
            (let [[v c] (alts! reads)]
              (if (or (= nil v) (= c change))
                  (do (when (= nil v)
                        (tset atom :cs c nil))
                      (loop (calc-state)))
                  (if (or (. solos c)
                          (and (not (next solos)) (not (. mutes c))))
                      (when (put! out v)
                        (loop state))
                      (loop state)))))
          (calc-state)))
    (doto m (tset :state atom) (tset :st calc-state))))

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

(defprotocol Pub
  (sub [_ v ch close?])
  (unsub [_ v ch])
  (unsub-all [_ v]))

(fn pub [ch topic-fn ?buf-fn]
  (let [buf-fn (or ?buf-fn #nil)
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
    (go #((fn loop []
            (let [val (take! ch)]
              (if (= nil val)
                  (each [_ m (pairs atom.mults)]
                    (close! (m:muxch)))
                  (let [topic (topic-fn val)]
                    (case (. atom :mults topic)
                      m (when (not (put! (m:muxch) val))
                          (tset atom :mults topic nil)))
                    (loop)))))))
    p))

(fn sub [p topic ch ...]
  {:fnl/docstring "Subscribes a channel to a topic of a pub.
By default the channel will be closed when the source closes,
but can be determined by the close? parameter."
   :fnl/arglist [p topic ch close?]}
  (let [close? (if (= (select :# ...) 0) true ...)]
    (p:sub topic ch close?)))

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
                (let [[v c] (alts! cs)]
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

 (let [a (chan 2)]
   (go #(alts! [[a :a] [a :b] nil]))
   (take! a pprint)
   (take! a pprint)
   )

 (do
   (local a (chan 10))
   (local b (chan 10))
   (put! a :a)
   (put! b :b)
   (go #(alts! [[a :c] [b :d] nil]))
   (put! a :e)
   (put! b :f)
   (take! a (partial print :from-a))
   (take! b (partial print :from-b))
   (take! a (partial print :from-a))
   (take! b (partial print :from-b))
   (take! a (partial print :from-a))
   (take! b (partial print :from-b))
   )

 (do
   (local a (chan 10))
   (local b (chan 10))
   (put! a :a)
   (put! b :b)
   (go #(pprint (alts! [a b])))
   )

 (let [c (chan)]
   (put! c 0)
   (pipe (to-chan! [1 2 3 4 5]) c)
   (take! (into [] c) pprint))

 (do
   (fn delayed-inc [v c]
     (go #(do (print :doing: v)
              (take! (timeout 1))
              (put! c (+ v 1))
              (close! c)
              (print :done: v))))
   (local data (to-chan! [1 2 3 4 5 6 7 8 9 10]))
   (local results (chan))
   (pipeline-async 10 results delayed-inc data true)
   (take! (into [] results) pprint)
   (while (not results.closed))
   )

 (do
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
   )

 (do
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

 (do (local c (chan 3))
     (go #(let [m (mix c)
                c1 (chan)
                c2 (chan)
                c3 (chan)]
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
