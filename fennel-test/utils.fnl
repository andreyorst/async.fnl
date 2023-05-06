(fn eq [...]
  "Comparison function.

Accepts arbitrary amount of values, and does the deep comparison.  If
values implement `__eq` metamethod, tries to use it, by checking if
first value is equal to second value, and the second value is equal to
the first value.  If values are not equal and are tables does the deep
comparison.  Tables as keys are supported."
  (match (select "#" ...)
    0 true
    1 true
    2 (let [(a b) ...]
        (if (and (= a b) (= b a))
            true
            (= :table (type a) (type b))
            (do (var (res count-a) (values true 0))
                (each [k v (pairs a) :until (not res)]
                  (set res (eq v (do (var (res done) (values nil nil))
                                     (each [k* v (pairs b) :until done]
                                       (when (eq k* k)
                                         (set (res done) (values v true))))
                                     res)))
                  (set count-a (+ count-a 1)))
                (when res
                  (let [count-b (accumulate [res 0 _ _ (pairs b)]
                                  (+ res 1))]
                    (set res (= count-a count-b))))
                res)
            false))
    _ (let [(a b) ...]
        (and (eq a b) (eq (select 2 ...))))))

(local view
  (match (pcall require :fennel)
    (true fennel) #(fennel.view $ {:one-line? true})
    _ tostring))

{: eq
 :tostring view}
