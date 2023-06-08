# `tap>`, `add-tap`, and `remove-tap`

Here's how Clojure's `tap>` can be implemented with channels:

```fennel
;; tap.fnl
(local {: chan : mult : tap : untap
        : close! : <! : offer!}
  (require :src.async))

(import-macros
 {: go : go-loop}
 (doto :src.async require))

(local tap-ch (chan))
(local mult-ch (mult tap-ch))
(local taps {})

(fn remove-tap [f]
  (case (. taps f)
    c (do (untap mult-ch c)
          (close! c)))
  (tset taps f nil))

(fn add-tap [f]
  (remove-tap f)
  (let [c (chan)]
    (tap mult-ch c)
    (go-loop []
      (let [data (<! c)]
        (when data
          (f data)
          (recur))))
    (tset taps f c)))

(fn tap> [x]
  (offer! tap-ch x))

{: add-tap
 : remove-tap
 : tap>}
```

It can be used in the REPL as follows:

```fennel
>> (local {: add-tap : tap> : remove-tap} (require :tap))
nil
>> (add-tap #(print "tap 1" $))
nil
>> (tap> 42)
tap 1	42
true
>> (add-tap #(print "tap 2" $))
nil
>> (tap> 42)
tap 1	42
tap 2	42
true
```

Functions supplied to `add-tap` should never block.
Functions have to be stored somewhere in order to remove taps.
