(require-macros (doto :fennel-test require))

(local {: buffer
        : dropping-buffer
        : sliding-buffer
        : promise-buffer
        : unblocking-buffer?}
  (require :src.async))

(deftest unblocking-buffer-tests
  (testing "buffers"
    (assert-not (unblocking-buffer? (buffer 1)))
    (assert-is (unblocking-buffer? (dropping-buffer 1)))
    (assert-is (unblocking-buffer? (sliding-buffer 1)))
    (assert-is (unblocking-buffer? (promise-buffer)))))

(deftest fixed-buffer-test
  (let [fb (buffer 2)]
    (assert-eq 0 (length fb))

    (fb:add! :1)
    (assert-eq 1 (length fb))

    (fb:add! :2)
    (assert-eq 2 (length fb))
    (assert-is (fb:full?))

    (fb:add! :3)
    (assert-eq 3 (length fb))
    (assert-is (fb:full?))

    (assert-eq :1 (fb:remove!))
    (assert-eq 2 (length fb))
    (assert-is (fb:full?))

    (assert-eq :2 (fb:remove!))
    (assert-eq 1 (length fb))
    (assert-not (fb:full?))

    (assert-eq :3 (fb:remove!))
    (assert-eq 0 (length fb))))

(deftest dropping-buffer-test
  (let [fb (dropping-buffer 2)]
    (assert-eq 0 (length fb))

    (fb:add! :1)
    (assert-eq 1 (length fb))

    (fb:add! :2)
    (assert-eq 2 (length fb))

    (assert-not (fb:full?))
    (fb:add! :3)

    (assert-eq 2 (length fb))

    (assert-eq :1 (fb:remove!))
    (assert-not (fb:full?))

    (assert-eq 1 (length fb))
    (assert-eq :2 (fb:remove!))

    (assert-eq 0 (length fb))))

(deftest sliding-buffer-test
  (let [fb (sliding-buffer 2)]
    (assert-eq 0 (length fb))

    (fb:add! :1)
    (assert-eq 1 (length fb))

    (fb:add! :2)
    (assert-eq 2 (length fb))

    (assert-not (fb:full?))
    (fb:add! :3)

    (assert-eq 2 (length fb))

    (assert-eq :2 (fb:remove!))
    (assert-not (fb:full?))

    (assert-eq 1 (length fb))
    (assert-eq :3 (fb:remove!))

    (assert-eq 0 (length fb))))

(deftest promise-buffer-tests
  (let [pb (promise-buffer)]
    (assert-eq 0 (length pb))

    (pb:add! :1)
    (assert-eq 1 (length pb))

    (pb:add! :2)
    (assert-eq 1 (length pb))

    (assert-not (pb:full?))

    (assert-eq 1 (length pb))

    (assert-eq :1 (pb:remove!))
    (assert-not (pb:full?))

    (assert-eq 1 (length pb))
    (assert-eq :1 (pb:remove!))

    (assert-eq :1 (pb:remove!))))
