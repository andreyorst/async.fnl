(comment
 "Copyright (c) 2023 Andrey Listopadov and contributors. All rights reserved.
The use and distribution terms for this software are covered by the
Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
which can be found in the file LICENSE at the root of this distribution.
By using this software in any fashion, you are agreeing to be bound by
the terms of this license.
You must not remove this notice, or any other, from this software.")

(fn assert-tail [tail-sym body]
  "Asserts that the passed in tail-sym function is a tail-call position of the
passed-in body.

Throws an error if it is in a position to be returned or if the function is
situated to be called from a position other than the tail of the passed-in
body."
  (fn last-arg? [form i]
    (= (- (length form) 1) i))

  ;; Tail in special forms are (After macroexpanding):
  ;;
  ;; - Every second form in an if, or the last form
  ;; (if ... (sym ...) (sym ...))
  ;;
  ;; - Last form in a let
  ;; (let [] (sym ...))
  ;;
  ;; - Last form in a do
  ;; (do ... (sym ...))
  ;;
  ;; Anything else fails the assert
  (fn path-tail? [op i form]
    (if (= op 'if) (and (not= 1 i) (or (last-arg? form i) (= 0 (% i 2))))
        (= op 'let) (last-arg? form i)
        (= op 'do) (last-arg? form i)
        false))

  ;; Check the current form for the tail-sym, and if it's in a bad
  ;; place, error out. If we run into other forms, we recurse with the
  ;; comprehension if this is the tail form or not
  (fn walk [body ok]
    (let [[op & operands] body]
      (if (list? op) (walk op true)
          (assert-compile (not (and (= tail-sym op) (not ok)))
                          (.. (tostring tail-sym) " must be in tail position")
                          op)
          (each [i v (ipairs operands)]
            (if (list? v) (walk v (and ok (path-tail? op i body)))
                (assert-compile (not= tail-sym v)
                                (.. (tostring tail-sym) " must not be passed")
                                v))))))

  (walk `(do ,(macroexpand body)) true))

(fn go-loop [bindings ...]
  {:fnl/arglist [bindings & body]
   :fnl/docstring "Asyncrhonous loop macro.

Similar to `let`, but binds a special `recur` call that will reassign
the values of the `bindings` and restart the loop `body` when called
in tail position.  Unlike `let`, doesn't support multiple-value
destructuring specifically."}
  (let [recur (sym :recur)
        keys []
        gensyms []
        bindings* []]
    (assert-tail recur ...)
    (for [i 2 (length bindings) 2]
      (let [v (. bindings i)
            key (. bindings (- i 1))
            gs (gensym (tostring i))]
        (assert-compile (not (list? key)) "go-loop macro doesn't support multiple-value destructuring" key)
        ;; [sym1# sym2# etc...], for the function application below
        (table.insert gensyms gs)

        ;; let bindings
        (table.insert bindings* gs)    ;; sym1#
        (table.insert bindings* v)     ;; (expression)
        (table.insert bindings* key)   ;; [first & rest]
        (table.insert bindings* gs)    ;; sym1#

        ;; The gensyms we use for function application
        (table.insert keys key)))
    `(let [{:go go#} (require :async)]
       (go# #(let ,bindings*
               ((fn ,recur ,keys
                  ,...)
                ,(table.unpack gensyms)))))))

(fn go [...]
  {:fnl/arglist [& body]
   :fnl/docstring "Asynchronously executes the `body`, returning immediately to the
calling thread. Additionally, any visible calls to `<!`, `>!` and
`alts!`  channel operations within the `body` will block (if
necessary) by 'parking' the calling thread rather than tying up the
only Lua thread.  Upon completion of the operation, the `body` will be
resumed.  Returns a channel which will receive the result of the `body`
when completed."}
  `(let [{:go go#} (require :async)]
     (go# #(do ,...))))

;; TODO alt!

{: go-loop
 : go}
