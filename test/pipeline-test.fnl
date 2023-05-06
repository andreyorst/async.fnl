(require-macros :fennel-test)
(local {: <! : >! : <!! : >!! : chan : close! : to-chan! : go
        : pipeline-async : pipeline : put! : timeout : alts! : into}
  (require :src.async))

(fn take!! [c tout]
  (<!! (go #(let [t (timeout (or tout 300))]
              (match (alts! [c t])
                [nil t] :timeout
                [_] _)))))

(fn pipeline-tester [pipeline-fn n inputs xf]
  (let [cin (to-chan! inputs)
        cout (chan 1)]
    (pipeline-fn n cout xf cin)
    (into [] cout)))

(fn identity-async [v ch]
  (go #(do (>! ch v) (close! ch))))

(fn map [f]
  (fn [rf]
    (fn [...]
      (case (select :# ...)
        0 (rf)
        1 (rf ...)
        _ (rf ... (f (select 2 ...)))))))

(fn test-size-async [n size]
  (let [r (fcollect [i 0 (- size 1)] i)]
    (assert-eq r (take!! (pipeline-tester pipeline-async n r identity-async)))))

(fn test-size-compute [n size]
  (let [r (fcollect [i 0 (- size 1)] i)]
    (assert-eq r (take!! (pipeline-tester pipeline n r (map #$))))))

(deftest pipeline-test-sizes
  (testing "pipeline async test sizes"
    (test-size-async 1 0)
    (test-size-async 1 10)
    (test-size-async 10 10)
    (test-size-async 20 10)
    (test-size-async 5 1000))
  (testing "pipeline compute test sizes"
    (test-size-compute 1 0)
    (test-size-compute 1 10)
    (test-size-compute 10 10)
    (test-size-compute 20 10)
    (test-size-compute 5 1000)))

(deftest test-close?
  (let [cout (chan 1)]
    (pipeline 5 cout (map #$) (to-chan! [1]) true)
    (assert-eq 1 (take!! cout))
    (assert-is cout.closed)
    (assert-eq nil (take!! cout)))
  (let [cout (chan 1)]
    (pipeline 5 cout (map #$) (to-chan! [1]) false)
    (assert-eq 1 (take!! cout))
    (assert-not cout.closed)
    (>!! cout :more)
    (assert-eq :more (take!! cout))))

(deftest test-ex-handler
  (let [cout (chan 1)
        chex (chan 1)
        ex-mapping (map (fn [x] (if (= x 3) (error {:data x}) x)))
        ex-handler (fn [e] (put! chex e) :err)]
    (pipeline 5 cout ex-mapping (to-chan! [1 2 3 4]) true ex-handler)
    (assert-eq 1 (take!! cout))
    (assert-eq 2 (take!! cout))
    (assert-eq :err (take!! cout))
    (assert-eq 4 (take!! cout))
    (assert-eq {:data 3} (take!! chex))))

(fn multiplier-async [v ch]
  (go #(do (for [i 0 (- v 1)] (>! ch i))
           (close! ch))))

(fn range [low up]
  (fcollect [i (if up low 0) (- (or up low) 1)] i))

(deftest async-pipelines-af-multiplier
  (assert-eq [0 0 1 0 1 2 0 1 2 3]
             (take!! (pipeline-tester pipeline-async 2 (range 1 5) multiplier-async) 5000)))

(fn incrementer-async [v ch]
  (go #(do (>! ch (+ 1 v))
           (close! ch))))

(deftest pipelines-async
  (assert-eq (range 1 101)
             (take!! (pipeline-tester pipeline-async 1 (range 100) incrementer-async))))

(fn slow-fib [n]
  (if (< n 2) n (+ (slow-fib (- n 1)) (slow-fib (- n 2)))))

(deftest pipelines-compute
  (let [input (faccumulate [res [] i 1 math.huge :until (= 50 (length res))]
                (fcollect [i 15 37 :into res :until (= 50 (length res))] i))
        last #(. $ (length $))]
    (assert-eq (slow-fib (last input))
               (last (take!! (pipeline-tester pipeline 8 input (map slow-fib)))))))
