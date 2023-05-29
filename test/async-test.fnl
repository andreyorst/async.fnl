(require-macros (doto :fennel-test require))

(local {: <! : >! : <!! : chan : close! : to-chan! : promise-chan
        : pipeline-async : pipeline : pipe : take! : put! : timeout
        : alts! : into : offer! : poll! &as async}
  (require :src.async))

(import-macros
 {: go : go-loop}
 (doto :src.async require))

(fn take!! [c tout val]
  (<!! (go (let [t (timeout (or tout 300))]
             (match (alts! [c t])
               [_ t] (or val :timeout)
               [_] _)))))

(deftest put-take-chan-1-test
  (let [c (chan 1 nil error)]
    (put! c 42)
    (take! c #(assert-eq 42 $))))

(deftest put-take-chan-test
  (let [c (chan nil nil error)]
    (put! c 42)
    (take! c #(assert-eq 42 $))))

(fn identity-chan [x]
  (let [c (chan 1)]
    (go (>! c x)
        (close! c))
    c))

(deftest identity-chan-test
  (->> (go
         (assert-eq 42 (<! (identity-chan 42)))
         true)
       take!!
       assert-is))

(deftest alts-tests
  (testing "alts! works at all"
    (let [c (identity-chan 42)]
      (go (assert-eq [42 c] (alts! [c])))))
  (testing "alts! can use default"
    (go
      (assert-eq
       [42 :default]
       (alts! [(chan 1)] :default 42)))))

(deftest timeout-tests
  (testing "timeout will return same channel if within delay"
    (assert-eq (timeout 10) (timeout 10))))

(deftest queue-limits
  (testing "async put!s are limited"
    (let [c (chan)]
      (for [x 1 1024]
        (put! c x))
      (assert-not (pcall put! c 42))
      (take! c (fn [x] (assert-is (= x 1))))))
  (testing "async take!s are limited"
    (let [c (chan)]
      (for [x 1 1024]
        (take! c (fn [x])))
      (assert-not (pcall take! c (fn [x])))
      (put! c 42))))

(deftest close-on-exception-tests
  (testing "go blocks"
    (go
      (let [c (go (assert false "This exception is expected"))
            t (timeout 500)]
        (assert-eq [nil c] (alts! [c t]))))))

(deftest cleanup
  (testing "alt handlers are removed from put!"
    (go
      (let [c (chan)]
        (for [x 1 1024]
          (alts! [[c x]] :default 42))
        (assert-is (put! c 42))))))

(deftest pipe-test
  (go
    (assert-eq [1 2 3 4 5]
               (let [out (chan)]
                 (async.pipe (async.to-chan! [1 2 3 4 5])
                             out)
                 (<! (into [] out))))))

(deftest split-test
  ;; Must provide buffers for channels else the tests won't complete
  (let [a (chan)
        b (chan)]
    (go
      (let [[even odd] (async.split
                        #(= 0 (% $ 2))
                        (async.to-chan! [1 2 3 4 5 6])
                        5 5)]
        (>! a (<! (into [] even)))
        (>! b (<! (into [] odd)))))
    (assert-eq [2 4 6] (take!! a))
    (assert-eq [1 3 5] (take!! b))))

(fn range [low up]
  (fcollect [i (if up low 0) (- (or up low) 1)] i))

(deftest map-test
  (assert-eq [0 4 8 12]
             (->> [(async.to-chan! (range 4))
                   (async.to-chan! (range 4))
                   (async.to-chan! (range 4))
                   (async.to-chan! (range 4))]
                  (async.map #(+ $1 $2 $3 $4))
                  (into [])
                  take!!)))

(fn frequencies [t]
  (accumulate [res {} _ v (pairs t)]
    (case (. res v)
      a (doto res (tset v (+ a 1)))
      _ (doto res (tset v 1)))))

(deftest merge-test
  (assert-eq {0 4 1 4 2 4 3 4}
             (->> [(async.to-chan! (range 4))
                   (async.to-chan! (range 4))
                   (async.to-chan! (range 4))
                   (async.to-chan! (range 4))]
                  async.merge
                  (into [])
                  take!!
                  frequencies)))

(deftest mult-test
  (let [a (chan 4)
        b (chan 4)
        src (chan)
        m (async.mult src)]
    (async.tap m a)
    (async.tap m b)
    (async.pipe (async.to-chan! (range 4)) src)
    (assert-eq [0 1 2 3] (take!! (into [] a)))
    (assert-eq [0 1 2 3] (take!! (into [] b)))))

(deftest mix-test
  (let [out (chan)
        mx (async.mix out)
        take-out (chan)
        take6 (go (for [x 1 6]
                    (>! take-out (<! out)))
                  (close! take-out))]
    (async.admix mx (async.to-chan! [1 2 3]))
    (async.admix mx (async.to-chan! [4 5 6]))
    (assert-eq [1 2 3 4 5 6]
               (doto (take!! (into [] take-out) nil [:timeout]) table.sort))))

(deftest pub-sub-test
  (let [a-ints (chan 5)
        a-strs (chan 5)
        b-ints (chan 5)
        b-strs (chan 5)
        src (chan)
        p (async.pub src (fn [x]
                           (if (= :string (type x))
                               :string
                               :int)))]
    (async.sub p :string a-strs)
    (async.sub p :string b-strs)
    (async.sub p :int a-ints)
    (async.sub p :int b-ints)
    (async.pipe (async.to-chan! [1 "a" 2 "b" 3 "c"]) src)
    (assert-eq [1 2 3]
               (take!! (into [] a-ints)))
    (assert-eq [1 2 3]
               (take!! (into [] b-ints)))
    (assert-eq ["a" "b" "c"]
               (take!! (into [] a-strs)))
    (assert-eq ["a" "b" "c"]
               (take!! (into [] b-strs)))))

(deftest reduce-test
  (->> []
       async.to-chan!
       (async.reduce #(+ $1 $2) 0)
       take!!
       (assert-eq 0))
  (->> 10
       range
       async.to-chan!
       (async.reduce #(+ $1 $2) 0)
       take!!
       (assert-eq 45))
  (->> 10
       range
       async.to-chan!
       (async.reduce #(if (= $2 2) (async.reduced :foo) $1) 0)
       take!!
       (assert-eq :foo)))

(deftest dispatch-bugs
  (testing "puts are moved to buffers"
    (let [c (chan 1)
          x (chan 1)
          atom {:a 0}]
      (put! c 42 (fn [_] (set atom.a (+ atom.a 1)) atom.a)) ;; Goes into buffer
      (put! c 42 (fn [_] (set atom.a (+ atom.a 1)) atom.a)) ;; Goes into puts
      (take! c
             (fn [_]
               ;; Should release the item in the puts and put its
               ;; value into the buffer, dispatching the callback
               (go
                 (<! (timeout 500))
                 (>! x atom.a))))
      (assert-eq 2 (take!! x 1000)))))

(fn integer-chan
  [n xform]
  "Returns a channel upon which will be placed integers from `0` to
`n` (exclusive) at 10 ms intervals, using the provided `xform`."
  (let [c (chan 1 xform)]
    (go-loop [i 0]
      (if (< i n)
          (do
            (<! (timeout 10))
            (>! c i)
            (recur (+ 1 i)))
          (close! c)))
    c))

(fn map [f]
  (fn [rf]
    (fn [...]
      (case (select :# ...)
        0 (rf)
        1 (rf ...)
        _ (rf ... (f (select 2 ...)))))))

(fn filter [f]
  (fn [rf]
    (fn [...]
      (case (select :# ...)
        0 (rf)
        1 (rf ...)
        _ (let [(result val) ...]
            (if (f val)
                (rf result val)
                result))))))

(fn partition-all [n]
  (fn [rf]
    (let [a {:n 0}]
      (fn [...]
        (case (select :# ...)
          0 (rf)
          1 (rf (if (= 0 a.n)
                    ...
                    (let [v (fcollect [i 1 a.n] (. a i))]
                      (each [k (pairs a)]
                        (tset a k nil))
                      (set a.n 0)
                      (rf ... v))))
          2 (let [(result input) ...]
              (tset a (+ a.n 1) input)
              (tset a :n (+ a.n 1))
              (if (= n a.n)
                  (let [v (fcollect [i 1 a.n] (. a i))]
                    (each [k (pairs a)]
                      (tset a k nil))
                    (set a.n 0)
                    (rf result v))
                  result)))))))

(fn cat [rf]
  (fn [...]
    (case (select :# ...)
      0 (rf)
      1 (rf ...)
      2 (let [(result input) ...]
          (accumulate [res result _ v (ipairs input)]
            (rf res v))))))

(fn comp [f g]
  #(f (g $...)))

(fn mapcat [f]
  (comp (map f) cat))

(deftest transducers-test
  (testing "base case without transducer"
    (assert-eq (range 10)
               (take!! (into [] (integer-chan 10 nil)) 2000)))
  (testing "mapping transducer"
    (assert-eq (icollect [_ v (ipairs (range 10))] (tostring v))
               (take!! (into [] (integer-chan 10 (map tostring))) 2000)))
  (testing "filtering transducer"
    (assert-eq (icollect [_ v (ipairs (range 10))] (when (= 0 (% v 2)) v))
               (take!! (into [] (integer-chan 10 (filter #(= 0 (% $ 2))))) 2000)))
  (testing "flatpmapping transducer"
    (let [pair-of (fn [x] [x x])]
      (assert-eq (accumulate [res [] _ v (ipairs (range 10))]
                   (doto res (table.insert v) (table.insert v)))
                 (take!! (into [] (integer-chan 10 (mapcat pair-of))) 2000))))
  (testing "partitioning transducer"
    (assert-eq [[0 1 2 3 4] [5 6 7]]
               (take!! (into [] (integer-chan 8 (partition-all 5))) 3000))
    (assert-eq [[0 1 2 3 4] [5 6 7 8 9]]
               (take!! (into [] (integer-chan 10 (partition-all 5))) 3000))))

(deftest bufferless-test
  (let [c (chan)
        res1 (chan)
        res2 (chan)]
    (go (>! res1 (async.alts! [c (timeout 400)] :priority true)))
    (go (>! res2 (async.alts! [[c :value] (timeout 400)] :priority true)))
    (assert-eq [:value c] (take!! res1 2100))
    (assert-eq [true c] (take!! res2 2100))))

(deftest promise-chan-test
  (testing "put on promise-chan fulfills all pending takers"
    (let [c  (promise-chan)
          t1 (go (<! c))
          t2 (go (<! c))]
      (put! c :val)
      (assert-eq :val (take!! t1))
      (assert-eq :val (take!! t2))
      (testing "then puts succeed but are dropped"
        (put! c :LOST)
        (assert-eq :val (take!! c)))
      (testing "then takes succeed with the original value"
        (assert-eq :val (take!! c))
        (assert-eq :val (take!! c))
        (assert-eq :val (take!! c)))
      (testing "then after close takes continue returning val"
        (close! c)
        (assert-eq :val (take!! c)))))
  (testing "close on promise-chan fulfills all pending takers"
    (let [c  (promise-chan)
          t3 (go (<! c))
          t4 (go (<! c))]
      (close! c)
      (assert-eq nil (take!! t3))
      (assert-eq nil (take!! t4))
      (testing "then takes return nil"
        (assert-eq nil (take!! t3))
        (assert-eq nil (take!! t3))
        (assert-eq nil (take!! t4))
        (assert-eq nil (take!! t4))
        (assert-eq nil (take!! c))
        (assert-eq nil (take!! c)))))
  (testing "close after put on promise-chan continues delivering promised value"
    (let [c (promise-chan)]
      (put! c :val) ;; deliver
      (assert-eq :val (take!! c))
      (assert-eq :val (take!! c))
      (close! c)
      (assert-eq :val (take!! c))
      (assert-eq :val (take!! c)))))

(deftest offer-poll-go-test
  (let [c (chan 2)]
    (assert-eq [true true 5 6 nil]
               [(offer! c 5) (offer! c 6) (poll! c) (poll! c) (poll! c)]))
  (let [c (chan 2)]
    (assert-is (offer! c 1))
    (assert-is (offer! c 2))
    (assert-eq nil (offer! c 3))
    (assert-eq 1 (poll! c))
    (assert-eq 2 (poll! c))
    (assert-eq nil (poll! c)))
  (let [c (chan)]
    (assert-eq nil (offer! c 1))
    (assert-eq nil (poll! c))))

(deftest transduce-test
  (assert-eq [1 2 3 4 5]
             (->> 5
                  range
                  async.to-chan!
                  (async.transduce (map #(+ $ 1)) #(doto $1 (table.insert $2)) [])
                  take!!)))

(var foo 42)

(deftest locals-alias-globals-test
  (let [c (chan 4)]
    (go (let [old foo]
          (set foo 45)
          (>! c (= foo 45))
          (>! c (= old 42))
          (set foo old)
          (>! c (= old 42))
          (>! c (= foo 42))
          (close! c)))
    (assert-eq [true true true true]
               (take!! (into [] c)))))

(deftest write-on-closed-test
  (let [closed (doto (chan) close!)
        open (chan)]
    (assert-eq
     :ok
     (->> (case (pcall #(for [i 1 3000] (alts! [open [closed true]] :priority true)))
            true :ok
            _ :not-ok)
          go
          take!!))))
