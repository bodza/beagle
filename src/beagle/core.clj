(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* aclone aget alength aset class defn doseq fn import keys let map merge meta ns-imports ns-resolve ns-unmap object-array select-keys seq seq? some? symbol symbol? var-get vary-meta])
    (:require [clojure.core :as -])
)

(-/defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (ns-imports *ns*))] (ns-unmap *ns* n#)) (import ~@syms-or-seqs)))

(import!
    [java.lang Appendable Character Error Integer Long Number String StringBuilder System]
    [java.io Flushable PrintWriter PushbackReader Reader]
    [java.util.regex Matcher Pattern]
    [clojure.lang IFn ISeq Namespace Seqable Var]
)

(-/defmacro refer! [ns s]
    (let [f (fn [%] (let [v (ns-resolve (-/the-ns ns) %) n (vary-meta % merge (select-keys (meta v) [:macro]))] `(def ~n ~(var-get v))))]
        (if (-/symbol? s) (f s) (-/cons 'do (map f s)))
    )
)

(refer! clojure.core [-> < <= == and bit-and bit-shift-left bit-shift-right char cond cons count declare defmacro identical? instance? int keyword? list map? name namespace or str the-ns unchecked-add-int unchecked-dec-int unchecked-inc-int unchecked-subtract-int var? when])

(defn throw! [#_"String" s] (throw (Error. s)))

(defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))

(defn char? [x] (instance? Character x))

(defn int? [x] (or (instance? Integer x) (instance? Long x)))

(defn #_"int" Integer'parseInt [#_"String" s] (Integer/parseInt s))

(defn number? [x] (instance? Number x))

(defn int! [^Number n] (.intValue n))

(defn #_"String" Number''toString [^Number this] (.toString this))

(defn string? [x] (instance? String x))

(defn #_"char"    String''charAt     [^String this, #_"int" i]    (.charAt this, i))
(defn #_"boolean" String''equals     [^String this, #_"any" that] (.equals this, that))
(defn #_"int"     String''indexOf   ([^String this, #_"int" c]    (.indexOf this, c))      ([^String this, #_"String" s, #_"int" from] (.indexOf this, s, from)))
(defn #_"int"     String''length     [^String this]               (.length this))
(defn #_"String"  String''substring ([^String this, #_"int" from] (.substring this, from)) ([^String this, #_"int" from, #_"int" over] (.substring this, from, over)))

(defn #_"StringBuilder" StringBuilder'new [] (StringBuilder.))

(defn #_"StringBuilder" StringBuilder''append   [^StringBuilder this, #_"char" ch] (.append this, ch))
(defn #_"String"        StringBuilder''toString [^StringBuilder this]              (.toString this))

(defn #_"void" System'arraycopy [#_"array" a, #_"int" i, #_"array" b, #_"int" j, #_"int" n] (System/arraycopy a, i, b, j, n))

(def System'in  *in*)
(def System'out *out*)

(defn array? [x] (and (some? x) (.isArray (class x))))

(defn #_"void" Flushable''flush [^Flushable this] (.flush this))

(defn #_"void" PushbackReader''unread [^PushbackReader this, #_"int" x] (.unread this, x))

(defn #_"int" Reader''read [^Reader this] (.read this))

(defn #_"Pattern" Pattern'compile  [#_"String" s]                (Pattern/compile s))
(defn #_"Matcher" Pattern''matcher [^Pattern this, #_"String" s] (.matcher this, s))

(defn #_"boolean" Matcher''matches [^Matcher this] (.matches this))

(defn clojure-fn? [x] (instance? clojure.lang.IFn x))

(defn #_"any" IFn''applyTo [^IFn this, #_"seq" args] (.applyTo this, args))

(defn clojure-seqable? [x] (instance? clojure.lang.Seqable x))

(defn #_"seq" Seqable''seq [^Seqable this] (.seq this))

(defn #_"any" ISeq''first [^ISeq this] (.first this))
(defn #_"seq" ISeq''next  [^ISeq this] (.next this))

(defn #_"var" Namespace''findInternedVar [^Namespace this, #_"Symbol" name] (.findInternedVar this, name))

(defn #_"any" Var''-get [^Var this] (.get this))

(defn A'new [n] (object-array n))

(defn A'clone  [^"[Ljava.lang.Object;" a]     (aclone a))
(defn A'get    [^"[Ljava.lang.Object;" a i]   (aget a i))
(defn A'length [^"[Ljava.lang.Object;" a]     (alength a))
(defn A'set    [^"[Ljava.lang.Object;" a i x] (aset a i x))

(def -seq     seq)
(def -seq?    seq?)
(def -symbol  symbol)
(def -symbol? symbol?)

(ns beagle.core
    (:refer-clojure :only [])
    (:require [beagle.bore :as -])
)

(-/import!)

(-/refer! beagle.bore [-> -seq -seq? -symbol -symbol? < <= == A'clone A'get A'length A'new A'set Appendable''append Flushable''flush IFn''applyTo ISeq''first ISeq''next Integer'parseInt Matcher''matches Namespace''findInternedVar Number''toString Pattern''matcher Pattern'compile PushbackReader''unread Reader''read Seqable''seq String''charAt String''equals String''indexOf String''length String''substring StringBuilder''append StringBuilder''toString StringBuilder'new System'arraycopy System'in System'out Var''-get and array? bit-and bit-shift-left bit-shift-right char char? clojure-fn? clojure-seqable? cond cons count declare identical? instance? int int! keyword? list map? name namespace number? or str string? the-ns throw! unchecked-add-int unchecked-dec-int unchecked-inc-int unchecked-subtract-int var? when])

(-/defmacro about [& s] (-/cons 'do s))

(-/defmacro λ    [& s] (-/cons 'fn* s))
(-/defmacro ζ    [& s] (-/cons 'fn* s))
(-/defmacro let  [& s] (-/cons 'let* s))
(-/defmacro loop [& s] (-/cons 'loop* s))

(def identical? -/identical?)

(def nil?  (λ [x] (identical? x nil)))
(def not   (λ [x] (if x false true)))
(def some? (λ [x] (not (nil? x))))

(about #_"beagle.Seqable"
    (declare cons?)

    (def seqable? (λ [x] (or (nil? x) (cons? x) (-/string? x) (-/clojure-seqable? x))))

    (declare Cons''seq)
    (declare str)

    (def seq (λ [x]
        (cond
            (nil? x)               nil
            (cons? x)              (Cons''seq x)
            (-/string? x)          (-/-seq x)
            (-/clojure-seqable? x) (-/Seqable''seq x)
            :else                  (-/throw! (str "seq not supported on " x))
        )
    ))
)

(about #_"beagle.ISeq"
    (def seq? (λ [x] (or (cons? x) (-/-seq? x))))

    (declare Cons''first)

    (def Seq''first (λ [s]
        (cond
            (cons? s)   (Cons''first s)
            (-/-seq? s) (-/ISeq''first s)
            :else       (-/throw! (str "first not supported on " s))
        )
    ))

    (declare Cons''next)

    (def Seq''next  (λ [s]
        (cond
            (cons? s)   (Cons''next s)
            (-/-seq? s) (-/ISeq''next s)
            :else       (-/throw! (str "next not supported on " s))
        )
    ))

    (def first (λ [s] (if (seq? s) (Seq''first s) (let [s (seq s)] (when (some? s) (Seq''first s))))))
    (def next  (λ [s] (if (seq? s) (Seq''next s)  (let [s (seq s)] (when (some? s) (Seq''next s))))))

    (def second (λ [s] (first (next s))))
    (def third  (λ [s] (first (next (next s)))))
    (def fourth (λ [s] (first (next (next (next s))))))

    (def reduce (λ [f r s] (let [s (seq s)] (if (some? s) (#_recur reduce f (f r (first s)) (next s)) r))))

    (def reduce-kv (λ [f r kvs] (let [kvs (seq kvs)] (if (some? kvs) (#_recur reduce-kv f (f r (first kvs) (second kvs)) (next (next kvs))) r))))
)

(about #_"beagle.Counted"
    (declare Cons''count)
    (declare inc)

    (def count (λ [x]
        (cond
            (nil? x)      0
            (cons? x)     (Cons''count x)
            (-/string? x) (-/String''length x)
            (seqable? x)  (loop [n 0 s (seq x)] (if (some? s) (recur (inc n) (next s)) n))
            :else         (-/throw! (str "count not supported on " x))
        )
    ))
)

(about #_"arrays"
    (def anew (λ [n] (-/A'new n)))

    (def aget    (λ [a i] (-/A'get a i)))
    (def alength (λ [a]   (-/A'length a)))

    (def aclone (λ [a]         (when (some? a) (-/A'clone a))))
    (def acopy! (λ [a i b j n] (-/System'arraycopy b, j, a, i, n) a))
    (def aset!  (λ [a i x]     (-/A'set a i x) a))

    (def volatile-acas! (λ [a i x y] (when (identical? (aget a i) x) (aset! a i y))))
    (def volatile-aget  (λ [a i]     (aget a i)))
    (def volatile-aset! (λ [a i x]   (aset! a i x)))
)

(about #_"unicode"
    (def Unicode'newline     10)
    (def Unicode'space       32)
    (def Unicode'quotation   34)
    (def Unicode'hash        35)
    (def Unicode'apostrophe  39)
    (def Unicode'lparen      40)
    (def Unicode'rparen      41)
    (def Unicode'plus        43)
    (def Unicode'comma       44)
    (def Unicode'minus       45)
    (def Unicode'slash       47)
    (def Unicode'0           48)
    (def Unicode'9           57)
    (def Unicode'colon       58)
    (def Unicode'lbracket    91)
    (def Unicode'backslash   92)
    (def Unicode'rbracket    93)
    (def Unicode'underscore  95)
    (def Unicode'grave       96)
    (def Unicode'n          110)
)

(about #_"append, str, pr, prn"
    (declare =)

    (def #_"char|String" escape-str (λ [#_"char" c]
        (cond
            (= (-/int c) Unicode'newline)   "\\n"
            (= (-/int c) Unicode'quotation) "\\\""
            (= (-/int c) Unicode'backslash) "\\\\"
            :else                           c
        )
    ))

    (def #_"Appendable" append-str (λ [#_"Appendable" a, #_"String" x]
        (let [
            a (-/Appendable''append a, "\"")
            a (reduce (λ [%1 %2] (-/Appendable''append %1, (escape-str %2))) a x)
            a (-/Appendable''append a, "\"")
        ]
            a
        )
    ))

    (declare Symbol''ns)
    (declare Symbol''name)

    (def #_"Appendable" append-sym (λ [#_"Appendable" a, #_"Symbol" x]
        (if (some? (Symbol''ns x))
            (let [
                a (-/Appendable''append a, (Symbol''ns x))
                a (-/Appendable''append a, "/")
                a (-/Appendable''append a, (Symbol''name x))
            ]
                a
            )
            (-/Appendable''append a, (Symbol''name x))
        )
    ))

    (def #_"Appendable" append* (λ [#_"Appendable" a, #_"String" b, #_"fn" f'append, #_"String" c, #_"String" d, #_"Seqable" q]
        (let [
            a (-/Appendable''append a, b)
            a
                (let [#_"seq" s (seq q)]
                    (if (some? s)
                        (loop [a a s s]
                            (let [a (f'append a (first s)) s (next s)]
                                (if (some? s) (recur (-/Appendable''append a, c) s) a)
                            )
                        )
                        a
                    )
                )
            a (-/Appendable''append a, d)
        ]
            a
        )
    ))

    (declare append)

    (def #_"Appendable" append-seq (λ [#_"Appendable" a, #_"seq" x] (append* a "(" append " " ")" x)))

    (declare symbol?)
    (declare atom?)

    (def #_"Appendable" append (λ [#_"Appendable" a, #_"any" x]
        (cond
            (= x nil)     (-/Appendable''append a, "nil")
            (= x false)   (-/Appendable''append a, "false")
            (= x true)    (-/Appendable''append a, "true")
            (-/number? x) (-/Appendable''append a, (-/Number''toString x))
            (-/string? x) (append-str a x)
            (symbol? x)   (append-sym a x)
            (cons? x)     (append-seq a x)
            (atom? x)     (-/Appendable''append a, "atom")
            :else         (-/Appendable''append a, "object")
        )
    ))

    (def #_"Appendable" append! (λ [#_"Appendable" a, #_"any" x]
        (if (or (-/-symbol? x) (-/string? x) (-/char? x)) (-/Appendable''append a, x) (append a x))
    ))

    (def #_"String" str (λ [& s]
        (loop [#_"StringBuilder" sb (-/StringBuilder'new) s s]
            (if (some? s)
                (let [x (first s)]
                    (recur (if (some? x) (append! sb x) sb) (next s))
                )
                (-/StringBuilder''toString sb)
            )
        )
    ))

    (def space   (λ [] (-/Appendable''append -/System'out (-/char Unicode'space))   nil))
    (def newline (λ [] (-/Appendable''append -/System'out (-/char Unicode'newline)) nil))
    (def flush   (λ [] (-/Flushable''flush   -/System'out)                          nil))

    (def pr (λ [& s]
        (when (some? s)
            (loop [x (first s) s (next s)]
                (append -/System'out x)
                (when (some? s)
                    (do
                        (space)
                        (recur (first s) (next s))
                    )
                )
            )
        )
        nil
    ))

    (def print (λ [& s]
        (when (some? s)
            (loop [x (first s) s (next s)]
                (append! -/System'out x)
                (when (some? s)
                    (do
                        (space)
                        (recur (first s) (next s))
                    )
                )
            )
        )
        nil
    ))

    (declare apply)

    (def prn     (λ [& s] (apply pr    s) (newline) (flush) nil))
    (def println (λ [& s] (apply print s) (newline) (flush) nil))
)

(about #_"beagle.Atom"

(about #_"Atom"
    (def Atom'meta (λ [] ))

    (def #_"Atom" Atom'new (λ [#_"any" init]
        (-> (anew 2) (aset! 0 Atom'meta) (volatile-aset! 1 init))
    ))

    (def atom? (λ [x] (and (-/array? x) (= (alength x) 2) (identical? (aget x 0) Atom'meta))))

    (def #_"any" Atom''deref (λ [#_"Atom" this]
        (volatile-aget this 1)
    ))

    (def #_"any" Atom''swap (λ [#_"Atom" this, #_"fn" f, #_"seq" s]
        (loop []
            (let [#_"any" o (volatile-aget this 1) #_"any" o' (apply f o s)]
                (if (volatile-acas! this 1 o o') o' (recur))
            )
        )
    ))

    (def #_"any" Atom''reset (λ [#_"Atom" this, #_"any" o']
        (volatile-aset! this 1 o')
        o'
    ))
)

(def atom (λ [x] (Atom'new x)))

(def deref (λ [a]
    (cond
        (atom? a) (Atom''deref a)
        :else     (-/throw! (str "deref not supported on " a))
    )
))

(def swap! (λ [a f & s]
    (cond
        (atom? a) (Atom''swap a, f, s)
        :else     (-/throw! (str "swap! not supported on " a))
    )
))

(def reset! (λ [a x]
    (cond
        (atom? a) (Atom''reset a, x)
        :else     (-/throw! (str "reset! not supported on " a))
    )
))
)

(about #_"equivalence"

(declare Symbol''equals)
(declare Cons''equals)

(def = (λ [x y]
    (cond
        (identical? x y) true
        (nil? x)         false
        (-/number? x)    (and (-/number? y) (-/== x y))
        (-/char? x)      (and (-/char? y) (-/== (-/int x) (-/int y)))
        (symbol? x)      (Symbol''equals x, y)
        (symbol? y)      (Symbol''equals y, x)
        (cons? x)        (Cons''equals x, y)
        (cons? y)        (Cons''equals y, x)
        (-/string? x)    (String''equals x, y)
        (-/-symbol? x)   (and (-/-symbol? y) (String''equals (-/str x), (-/str y)))
        (-/keyword? x)   (and (-/keyword? y) (String''equals (-/str x), (-/str y)))
        :else            (-/throw! (-/str "= not supported on " x ", not even on " y))
    )
))

(def not= (λ [x y] (not (= x y))))
)

(about #_"beagle.Numbers"

(def + (λ [x y] (-/unchecked-add-int (-/int! x) (-/int! y))))
(def - (λ [x y] (-/unchecked-subtract-int (-/int! x) (-/int! y))))

(def inc -/unchecked-inc-int)
(def dec -/unchecked-dec-int)

(def & (λ [x y] (-/int! (-/bit-and x y))))

(def << (λ [x y] (-/int! (-/bit-shift-left x y))))
(def >> (λ [x y] (-/int! (-/bit-shift-right x y))))

(def < -/<)
(def <= -/<=)

(def max (λ [x y] (if (< y x) x y)))
(def min (λ [x y] (if (< x y) x y)))

(def neg? (λ [n] (< n 0)))
(def zero? (λ [n] (= n 0)))
(def pos? (λ [n] (< 0 n)))

(def abs (λ [a] (if (neg? a) (- 0 a) a)))
)

(about #_"beagle.Symbol"

(about #_"Symbol"
    (def Symbol'meta (λ [] ))

    (def #_"Symbol" Symbol'new (λ [#_"String" ns, #_"String" name]
        (-> (anew 3) (aset! 0 Symbol'meta) (aset! 1 ns) (aset! 2 name))
    ))

    (def symbol? (λ [x] (and (-/array? x) (= (alength x) 3) (identical? (aget x 0) Symbol'meta))))

    (def #_"String" Symbol''ns   (λ [#_"Symbol" this] (when (symbol? this) (aget this 1))))
    (def #_"String" Symbol''name (λ [#_"Symbol" this] (when (symbol? this) (aget this 2))))

    (def #_"Symbol" Symbol'intern (λ [#_"String" nsname]
        (let [#_"int" i (-/String''indexOf nsname, Unicode'slash)]
            (if (or (= i -1) (= nsname "/"))
                (Symbol'new nil, nsname)
                (Symbol'new (-/String''substring nsname, 0, i), (-/String''substring nsname, (inc i)))
            )
        )
    ))

    (def #_"boolean" Symbol''equals (λ [#_"Symbol" this, #_"any" that]
        (or (identical? this that)
            (and (or (symbol? that) (-/-symbol? that))
                (= (Symbol''ns this) (if (-/-symbol? that) (-/namespace that) (Symbol''ns that)))
                (= (Symbol''name this) (if (-/-symbol? that) (-/name that) (Symbol''name that)))
            )
            (and (-/keyword? that)
                (= (Symbol''name this) (-/str that))
            )
        )
    ))
)

(def symbol (λ [name] (if (or (symbol? name) (-/-symbol? name)) name (Symbol'intern name))))

(def symbol! (λ [s] (symbol (if (-/-symbol? s) (str s) s))))
)

(about #_"beagle.Cons"

(about #_"Cons"
    (def Cons'meta (λ [] ))

    (def #_"Cons" Cons'new (λ [#_"any" car, #_"seq" cdr]
        (-> (anew 3) (aset! 0 Cons'meta) (aset! 1 car) (aset! 2 cdr))
    ))

    (def cons? (λ [x] (and (-/array? x) (= (alength x) 3) (identical? (aget x 0) Cons'meta))))

    (def #_"any" Cons''car (λ [#_"Cons" this] (when (cons? this) (aget this 1))))
    (def #_"seq" Cons''cdr (λ [#_"Cons" this] (when (cons? this) (aget this 2))))

    (def #_"Cons" Cons'nil (Cons'new nil, nil))

    (def #_"seq" Cons''seq (λ [#_"Cons" this]
        (if (identical? this Cons'nil) nil this)
    ))

    (def #_"any" Cons''first (λ [#_"Cons" this]      (Cons''car this)))
    (def #_"seq" Cons''next  (λ [#_"Cons" this] (seq (Cons''cdr this))))

    (def #_"int" Cons''count (λ [#_"Cons" this]
        (if (identical? this Cons'nil) 0 (inc (count (Cons''cdr this))))
    ))

    (def #_"boolean" Cons''equals (λ [#_"Cons" this, #_"any" that]
        (or (identical? this that)
            (and (some? that) (seqable? that)
                (loop [#_"seq" s (seq this) #_"seq" z (seq that)]
                    (if (some? s)
                        (and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                        (nil? z)
                    )
                )
            )
        )
    ))
)

(def cons (λ [x s] (Cons'new x, (seq s))))

(def spread (λ [s]
    (cond
        (nil? s) nil
        (nil? (next s)) (seq (first s))
        :else (cons (first s) (spread (next s)))
    )
))

(def reverse (λ [s] (reduce (λ [%1 %2] (cons %2 %1)) Cons'nil s)))

(def list (λ [& s] (if (some? s) (reverse (reverse s)) Cons'nil)))

(def reverse! (λ [s] (reduce (λ [%1 %2] (-/cons %2 %1)) (-/list) s)))

(about #_"Cons"
    (def #_"seq" Cons''keys (λ [#_"Cons" this]
        (loop [#_"seq" z nil #_"seq" s (seq this)]
            (if (some? s)
                (recur (cons (first s) z) (next (next s)))
                (when (some? z) (reverse z))
            )
        )
    ))

    (def #_"seq" Cons''vals (λ [#_"Cons" this]
        (loop [#_"seq" z nil #_"seq" s (seq this)]
            (if (some? s)
                (recur (cons (second s) z) (next (next s)))
                (when (some? z) (reverse z))
            )
        )
    ))
)

(def some (λ [f s]
    (when (seq s)
        (or (f (first s)) (#_recur some f (next s)))
    )
))
)

(about #_"beagle.ArrayMap"

(about #_"ArrayMap"
    (def ArrayMap'meta (λ [] ))

    (def #_"ArrayMap" ArrayMap'new (λ [#_"array" a]
        (-> (anew 2) (aset! 0 ArrayMap'meta) (aset! 1 (or a (anew 0))))
    ))

    (def array-map? (λ [x] (and (-/array? x) (= (alength x) 2) (identical? (aget x 0) ArrayMap'meta))))

    (def #_"array" ArrayMap''array (λ [#_"ArrayMap" this] (when (array-map? this) (aget this 1))))

    (def #_"ArrayMap" ArrayMap'EMPTY (ArrayMap'new nil))

    (def #_"ArrayMap" ArrayMap'create (λ [#_"array" a]
        (if (and (some? a) (pos? (alength a))) (ArrayMap'new a) ArrayMap'EMPTY)
    ))

    (def #_"int" ArrayMap'index-of (λ [#_"array" a, #_"key" key]
        (loop [#_"int" i 0]
            (if (< i (alength a))
                (if (= (aget a i) key) i (recur (+ i 2)))
                -1
            )
        )
    ))

    (def #_"value" ArrayMap''valAt (λ [#_"ArrayMap" this, #_"key" key]
        (let [
            #_"array" a (ArrayMap''array this) #_"int" i (ArrayMap'index-of a, key)
        ]
            (when (< -1 i)
                (aget a (inc i))
            )
        )
    ))

    (def #_"ArrayMap" ArrayMap''assoc (λ [#_"ArrayMap" this, #_"key" key, #_"value" val]
        (let [
            #_"array" a (ArrayMap''array this) #_"int" i (ArrayMap'index-of a, key)
        ]
            (if (< -1 i)
                (if (#_= identical? (aget a (inc i)) val)
                    this
                    (ArrayMap'new (aset! (aclone a) (inc i) val))
                )
                (let [
                    #_"int" n (alength a)
                    #_"array" a' (anew (+ n 2))
                    a' (if (pos? n) (acopy! a' 0 a 0 n) a')
                ]
                    (ArrayMap'new (aset! (aset! a' n key) (inc n) val))
                )
            )
        )
    ))

    (def #_"boolean" ArrayMap''containsKey (λ [#_"ArrayMap" this, #_"key" key]
        (< -1 (ArrayMap'index-of (ArrayMap''array this), key))
    ))
)

(def assoc (λ [m k v]
    (cond
        (nil? m)       (ArrayMap'new (-> (anew 2) (aset! 0 k) (aset! 1 v)))
        (array-map? m) (ArrayMap''assoc m, k, v)
        :else          (-/throw! (str "assoc not supported on " m))
    )
))

(def array-map (λ [& kvs] (if (some? kvs) (reduce-kv assoc ArrayMap'EMPTY kvs) ArrayMap'EMPTY)))

(def contains? (λ [m k]
    (cond
        (nil? m)       false
        (array-map? m) (ArrayMap''containsKey m, k)
        :else          (-/throw! (str "contains? not supported on " m))
    )
))

(def get (λ [m k]
    (cond
        (nil? m)       nil
        (array-map? m) (ArrayMap''valAt m, k)
        :else          (-/throw! (str "get not supported on " m))
    )
))

(def update (λ [m k f & s] (assoc m k (apply f (get m k) s))))
)

(about #_"beagle.Var"

(about #_"Var"
    (def #_"Var" Var'new (λ []
        (atom nil)
    ))

    (def #_"any" Var''get (λ [#_"Var" this]
        (if (-/var? this) (-/Var''-get this) (deref this))
    ))

    (def #_"void" Var''bindRoot (λ [#_"Var" this, #_"any" root]
        (reset! this root)
        nil
    ))
)
)

(about #_"beagle.Compiler"

(about #_"asm"
    (def #_"gen" Gen'new (λ [] nil))

    (def #_"label" Gen''label (λ [#_"gen" gen] (atom nil)))

    (def #_"gen" Gen''mark! (λ [#_"gen" gen, #_"label" label] (reset! label (count gen)) gen))

    (def #_"gen" Gen''anew     (λ [#_"gen" gen]                  (cons [:anew] gen)))
    (def #_"gen" Gen''apply    (λ [#_"gen" gen]                  (cons [:apply] gen)))
    (def #_"gen" Gen''aset     (λ [#_"gen" gen]                  (cons [:aset] gen)))
    (def #_"gen" Gen''create   (λ [#_"gen" gen, #_"FnExpr" fun]  (cons [:create fun] gen)))
    (def #_"gen" Gen''dup      (λ [#_"gen" gen]                  (cons [:dup] gen)))
    (def #_"gen" Gen''get      (λ [#_"gen" gen, #_"Symbol" name] (cons [:get name] gen)))
    (def #_"gen" Gen''goto     (λ [#_"gen" gen, #_"label" label] (cons [:goto label] gen)))
    (def #_"gen" Gen''if-eq?   (λ [#_"gen" gen, #_"label" label] (cons [:if-eq? label] gen)))
    (def #_"gen" Gen''if-nil?  (λ [#_"gen" gen, #_"label" label] (cons [:if-nil? label] gen)))
    (def #_"gen" Gen''invoke-1 (λ [#_"gen" gen, #_"fn" f]        (cons [:invoke-1 f] gen)))
    (def #_"gen" Gen''invoke-2 (λ [#_"gen" gen, #_"fn" f]        (cons [:invoke-2 f] gen)))
    (def #_"gen" Gen''pop      (λ [#_"gen" gen]                  (cons [:pop] gen)))
    (def #_"gen" Gen''push     (λ [#_"gen" gen, #_"value" value] (cons [:push value] gen)))
    (def #_"gen" Gen''return   (λ [#_"gen" gen]                  (cons [:return] gen)))
)

(about #_"Compiler"
    (declare Expr''emit)

    (def #_"gen" Compiler'emitArgs (λ [#_"map" scope, #_"gen" gen, #_"Expr*" args]
        (let [
            gen (Gen''push gen, (count args))
            gen (Gen''anew gen)
        ]
            (loop [gen gen #_"int" i 0 #_"seq" s (seq args)]
                (if (some? s)
                    (let [
                        gen (Gen''dup gen)
                        gen (Gen''push gen, i)
                        gen (Expr''emit (first s), :Context'EXPRESSION, scope, gen)
                        gen (Gen''aset gen)
                    ]
                        (recur gen (inc i) (next s))
                    )
                    gen
                )
            )
        )
    ))

    (declare Binding''sym)
    (declare Binding''idx)

    (def #_"gen" Compiler'emitLocal (λ [#_"map" scope, #_"gen" gen, #_"Binding" lb]
        (Gen''get gen, (Binding''sym lb))
    ))

    (def #_"gen" Compiler'emitLocals (λ [#_"map" scope, #_"gen" gen, #_"Binding*" locals]
        (let [
            gen (Gen''push gen, (<< (count locals) 1))
            gen (Gen''anew gen)
        ]
            (loop [gen gen #_"int" i 0 #_"seq" s (seq locals)]
                (if (some? s)
                    (let [
                        #_"Binding" lb (first s)
                        gen (Gen''dup gen)
                        gen (Gen''push gen, i)
                        gen (Gen''push gen, (Binding''sym lb))
                        gen (Gen''aset gen)
                        i (inc i)
                        gen (Gen''dup gen)
                        gen (Gen''push gen, i)
                        gen (Compiler'emitLocal scope, gen, lb)
                        gen (Gen''aset gen)
                        i (inc i)
                    ]
                        (recur gen i (next s))
                    )
                    gen
                )
            )
        )
    ))
)

(about #_"beagle.Closure"

(about #_"Closure"
    (def Closure'meta (λ [] ))

    (def #_"Closure" Closure'new (λ [#_"FnExpr" fun, #_"map" env]
        (-> (anew 3) (aset! 0 Closure'meta) (aset! 1 fun) (aset! 2 env))
    ))

    (def closure? (λ [x] (and (-/array? x) (= (alength x) 3) (identical? (aget x 0) Closure'meta))))

    (def #_"FnExpr" Closure''fun (λ [#_"Closure" this] (when (closure? this) (aget this 1))))
    (def #_"map"    Closure''env (λ [#_"Closure" this] (when (closure? this) (aget this 2))))

    (declare Machine'compute)
    (declare FnExpr''compile)

    (def #_"any" Closure''applyTo (λ [#_"Closure" this, #_"seq" args]
        (let [
            #_"FnExpr" fun (Closure''fun this) #_"int" n (get fun :arity)
            _
                (let [#_"int" m (count args)]
                    (when (< m (dec (- 0 n)))
                        (-/throw! (str "wrong number of args (" m ") passed to " this))
                    )
                )
            #_"map" env
                (let [n (if (neg? n) (- 0 n) (inc n))]
                    (loop [env (Closure''env this) #_"int" i 0 #_"seq" s (seq args)]
                        (let [#_"Binding" lb (some (λ [%] (when (= (Binding''idx %) i) %)) (get fun :locals))]
                            (if (zero? i)
                                (recur (if (some? lb) (assoc env (Binding''sym lb) this) env) (inc i) s)
                                (if (< i n)
                                    (recur (assoc env (Binding''sym lb) (first s)) (inc i) (next s))
                                    (if (some? s) (assoc env (Binding''sym lb) s) env)
                                )
                            )
                        )
                    )
                )
        ]
            (Machine'compute (FnExpr''compile fun), env)
        )
    ))
)

(def apply (λ [f & s]
    (let [s (spread s)]
        (cond
            (closure? f)      (Closure''applyTo f, s)
            (atom? f)         (apply (deref f) s)
            (-/clojure-fn? f) (-/IFn''applyTo f, (when (seq s) (reverse! (reverse s))))
            :else             (-/throw! (str "apply not supported on " f))
        )
    )
))
)

(about #_"LiteralExpr"
    (def LiteralExpr'meta (λ [] ))

    (def #_"LiteralExpr" LiteralExpr'new (λ [#_"any" value]
        (array-map
            #_"meta" :meta LiteralExpr'meta
            #_"any" :value value
        )
    ))

    (def #_"LiteralExpr" LiteralExpr'NIL   (LiteralExpr'new nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (LiteralExpr'new true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (LiteralExpr'new false))

    (def #_"Expr" LiteralExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (dec (count form))]
            (if (= n 1)
                (let [#_"any" x (second form)]
                    (cond
                        (= x nil)    LiteralExpr'NIL
                        (= x true)   LiteralExpr'TRUE
                        (= x false)  LiteralExpr'FALSE
                        :else       (LiteralExpr'new x)
                    )
                )
                (-/throw! (str "wrong number of arguments passed to quote: " n))
            )
        )
    ))

    (def #_"gen" LiteralExpr''emit (λ [#_"LiteralExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (if (not= context :Context'STATEMENT) (Gen''push gen, (get this :value)) gen)
    ))
)

(about #_"VarExpr"
    (def VarExpr'meta (λ [] ))

    (def #_"VarExpr" VarExpr'new (λ [#_"Var" var]
        (array-map
            #_"meta" :meta VarExpr'meta
            #_"Var" :var var
        )
    ))

    (def #_"gen" VarExpr''emit (λ [#_"VarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (get this :var))
            gen (Gen''invoke-1 gen, Var''get)
        ]
            (if (= context :Context'STATEMENT)
                (Gen''pop gen)
                gen
            )
        )
    ))
)

(about #_"BodyExpr"
    (def BodyExpr'meta (λ [] ))

    (def #_"BodyExpr" BodyExpr'new (λ [#_"Expr*" exprs]
        (array-map
            #_"meta" :meta BodyExpr'meta
            #_"Expr*" :exprs exprs
        )
    ))

    (declare Compiler'analyze)

    (def #_"Expr" BodyExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"seq" s form s (if (= (first s) 'do) (next s) s)
            #_"Expr*" z
                (loop [z nil s s]
                    (if (some? s)
                        (let [#_"Context" c (if (or (= context :Context'STATEMENT) (some? (next s))) :Context'STATEMENT context)]
                            (recur (cons (Compiler'analyze (first s), c, scope) z) (next s))
                        )
                        (reverse z)
                    )
                )
        ]
            (BodyExpr'new (or (seq z) (list LiteralExpr'NIL)))
        )
    ))

    (def #_"gen" BodyExpr''emit (λ [#_"BodyExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (loop [gen gen #_"seq" s (seq (get this :exprs))]
            (if (some? (next s))
                (recur (Expr''emit (first s), :Context'STATEMENT, scope, gen) (next s))
                (Expr''emit (first s), context, scope, gen)
            )
        )
    ))
)

(about #_"IfExpr"
    (def IfExpr'meta (λ [] ))

    (def #_"IfExpr" IfExpr'new (λ [#_"Expr" test, #_"Expr" then, #_"Expr" else]
        (array-map
            #_"meta" :meta IfExpr'meta
            #_"Expr" :test test
            #_"Expr" :then then
            #_"Expr" :else else
        )
    ))

    (def #_"Expr" IfExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (cond
            (< 4 (count form)) (-/throw! "too many arguments to if")
            (< (count form) 4) (-/throw! "too few arguments to if")
        )
        (let [
            #_"Expr" test (Compiler'analyze (second form), :Context'EXPRESSION, scope)
            #_"Expr" then (Compiler'analyze (third form), context, scope)
            #_"Expr" else (Compiler'analyze (fourth form), context, scope)
        ]
            (IfExpr'new test, then, else)
        )
    ))

    (def #_"gen" IfExpr''emit (λ [#_"IfExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            #_"label" l'nil (Gen''label gen) #_"label" l'false (Gen''label gen) #_"label" l'end (Gen''label gen)
            gen (Expr''emit (get this :test), :Context'EXPRESSION, scope, gen)
            gen (Gen''dup gen)
            gen (Gen''if-nil? gen, l'nil)
            gen (Gen''push gen, false)
            gen (Gen''if-eq? gen, l'false)
            gen (Expr''emit (get this :then), context, scope, gen)
            gen (Gen''goto gen, l'end)
            gen (Gen''mark! gen, l'nil)
            gen (Gen''pop gen)
            gen (Gen''mark! gen, l'false)
            gen (Expr''emit (get this :else), context, scope, gen)
            gen (Gen''mark! gen, l'end)
        ]
            gen
        )
    ))
)

(about #_"InvokeExpr"
    (def InvokeExpr'meta (λ [] ))

    (def #_"InvokeExpr" InvokeExpr'new (λ [#_"Expr" fexpr, #_"Expr*" args]
        (array-map
            #_"meta" :meta InvokeExpr'meta
            #_"Expr" :fexpr fexpr
            #_"Expr*" :args args
        )
    ))

    (def #_"Expr" InvokeExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"Expr" fexpr (Compiler'analyze (first form), :Context'EXPRESSION, scope)
            #_"Expr*" args (reverse (reduce (λ [%1 %2] (cons (Compiler'analyze %2, :Context'EXPRESSION, scope) %1)) nil (next form)))
        ]
            (InvokeExpr'new fexpr, args)
        )
    ))

    (def #_"gen" InvokeExpr''emit (λ [#_"InvokeExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Expr''emit (get this :fexpr), :Context'EXPRESSION, scope, gen)
            gen (Compiler'emitArgs scope, gen, (get this :args))
            gen (Gen''apply gen)
        ]
            (if (= context :Context'STATEMENT)
                (Gen''pop gen)
                gen
            )
        )
    ))
)

(about #_"Binding"
    (def Binding'meta (λ [] ))

    (def #_"Binding" Binding'new (λ [#_"Symbol" sym, #_"int" idx]
        (-> (anew 3) (aset! 0 Binding'meta) (aset! 1 sym) (aset! 2 idx))
    ))

    (def local-binding? (λ [x] (and (-/array? x) (= (alength x) 3) (identical? (aget x 0) Binding'meta))))

    (def #_"Symbol" Binding''sym (λ [#_"Binding" this] (when (local-binding? this) (aget this 1))))
    (def #_"int"    Binding''idx (λ [#_"Binding" this] (when (local-binding? this) (aget this 2))))
)

(about #_"BindingExpr"
    (def BindingExpr'meta (λ [] ))

    (def #_"BindingExpr" BindingExpr'new (λ [#_"Binding" lb]
        (array-map
            #_"meta" :meta BindingExpr'meta
            #_"Binding" :lb lb
        )
    ))

    (def #_"gen" BindingExpr''emit (λ [#_"BindingExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (if (not= context :Context'STATEMENT) (Compiler'emitLocal scope, gen, (get this :lb)) gen)
    ))
)

(about #_"FnExpr"
    (def FnExpr'meta (λ [] ))

    (def #_"FnExpr" FnExpr'new (λ [#_"FnExpr" parent]
        (array-map
            #_"meta" :meta FnExpr'meta
            #_"FnExpr" :parent parent
            #_"Binding*" :locals nil
            #_"Binding*'" :'closes (atom nil)
            #_"int" :arity nil
            #_"Expr" :body nil
        )
    ))

    (def #_"FnExpr" FnExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"symbol?" name (second form) ? (or (symbol? name) (-/-symbol? name)) name (when ? name) form (if ? (next (next form)) (next form))
            scope (update scope :fun FnExpr'new)
            scope
                (if (some? name)
                    (let [
                        #_"Binding" lb (Binding'new name, 0)
                        scope (update scope :local-env assoc (Binding''sym lb) lb)
                        scope (update scope :fun update :locals (λ [%] (cons lb %)))
                    ]
                        scope
                    )
                    scope
                )
            scope
                (loop [scope scope #_"int" arity 0 #_"boolean" variadic? false #_"seq" s (seq (first form))]
                    (if (some? s)
                        (let [#_"symbol?" sym (first s)]
                            (if (or (symbol? sym) (-/-symbol? sym))
                                (if (nil? (Symbol''ns sym))
                                    (cond
                                        (= sym '&)
                                            (if (not variadic?)
                                                (recur scope arity true (next s))
                                                (-/throw! "overkill variadic parameter list")
                                            )
                                        (neg? arity)
                                            (-/throw! (str "excess variadic parameter: " sym))
                                        :else
                                            (let [
                                                arity (if (not variadic?) (inc arity) (- 0 (inc arity)))
                                                #_"Binding" lb (Binding'new sym, (abs arity))
                                                scope (update scope :local-env assoc (Binding''sym lb) lb)
                                                scope (update scope :fun update :locals (λ [%] (cons lb %)))
                                            ]
                                                (recur scope arity variadic? (next s))
                                            )
                                    )
                                    (-/throw! (str "can't use qualified name as parameter: " sym))
                                )
                                (-/throw! "function parameters must be symbols")
                            )
                        )
                        (if (and variadic? (not (neg? arity)))
                            (-/throw! "missing variadic parameter")
                            (update scope :fun assoc :arity arity)
                        )
                    )
                )
        ]
            (assoc (get scope :fun) :body (BodyExpr'parse (next form), :Context'RETURN, scope))
        )
    ))

    (def #_"gen" FnExpr''emit (λ [#_"FnExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (if (not= context :Context'STATEMENT)
            (let [
                gen (Compiler'emitLocals scope, gen, (deref (get this :'closes)))
                gen (Gen''invoke-1 gen, ArrayMap'create)
            ]
                (Gen''create gen, this)
            )
            gen
        )
    ))

    (def #_"array" FnExpr''compile (λ [#_"FnExpr" this]
        (let [
            #_"map" scope (array-map :fun this)
            #_"gen" gen (Gen'new)
            gen (Expr''emit (get this :body), :Context'RETURN, scope, gen)
            gen (Gen''return gen)
        ]
            (loop [#_"array" a (anew (count gen)) #_"int" i 0 #_"seq" s (seq (reverse gen))]
                (if (some? s) (recur (aset! a i (first s)) (inc i) (next s)) a)
            )
        )
    ))
)

(about #_"DefExpr"
    (def DefExpr'meta (λ [] ))

    (def #_"DefExpr" DefExpr'new (λ [#_"Var" var, #_"Expr" init, #_"boolean" initProvided]
        (array-map
            #_"meta" :meta DefExpr'meta
            #_"Var" :var var
            #_"Expr" :init init
            #_"boolean" :initProvided initProvided
        )
    ))

    (def #_"{Symbol Var}'" Beagle'ns (atom (array-map)))

    (def #_"Var" DefExpr'lookupVar (λ [#_"Symbol" sym]
        (let [sym (symbol! sym)]
            (if (nil? (Symbol''ns sym))
                (or
                    (get (deref Beagle'ns) sym)
                    (let [#_"var" v (Var'new)]
                        (swap! Beagle'ns assoc sym v)
                        v
                    )
                )
                (-/throw! "can't create defs outside of current ns")
            )
        )
    ))

    (def #_"Expr" DefExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (count form)]
            (cond
                (< 3 n) (-/throw! "too many arguments to def")
                (< n 2) (-/throw! "too few arguments to def")
                :else
                    (let [#_"symbol?" s (second form)]
                        (if (or (symbol? s) (-/-symbol? s))
                            (DefExpr'new (DefExpr'lookupVar s), (Compiler'analyze (third form), :Context'EXPRESSION, scope), (= n 3))
                            (-/throw! "first argument to def must be a symbol")
                        )
                    )
            )
        )
    ))

    (def #_"gen" DefExpr''emit (λ [#_"DefExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (get this :var))
            gen
                (if (get this :initProvided)
                    (let [
                        gen (Gen''dup gen)
                        gen (Expr''emit (get this :init), :Context'EXPRESSION, scope, gen)
                        gen (Gen''invoke-2 gen, Var''bindRoot)
                    ]
                        (Gen''pop gen)
                    )
                    gen
                )
        ]
            (if (= context :Context'STATEMENT)
                (Gen''pop gen)
                gen
            )
        )
    ))
)

(about #_"Expr"
    (def #_"gen" Expr''emit (λ [#_"Expr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [#_"meta" m (get this :meta)]
            (cond
                (identical? m LiteralExpr'meta) (LiteralExpr''emit this, context, scope, gen)
                (identical? m VarExpr'meta)     (VarExpr''emit this, context, scope, gen)
                (identical? m BodyExpr'meta)    (BodyExpr''emit this, context, scope, gen)
                (identical? m IfExpr'meta)      (IfExpr''emit this, context, scope, gen)
                (identical? m InvokeExpr'meta)  (InvokeExpr''emit this, context, scope, gen)
                (identical? m BindingExpr'meta) (BindingExpr''emit this, context, scope, gen)
                (identical? m FnExpr'meta)      (FnExpr''emit this, context, scope, gen)
                (identical? m DefExpr'meta)     (DefExpr''emit this, context, scope, gen)
                :else                           (-/throw! (str "Expr''emit not supported on " this))
            )
        )
    ))
)

(about #_"Compiler"
    (def #_"map" Compiler'specials
        (array-map
            '&          nil
            'def        DefExpr'parse
            'do         BodyExpr'parse
            'λ          FnExpr'parse            'ζ          FnExpr'parse
            'if         IfExpr'parse
            'quote      LiteralExpr'parse
        )
    )

    (def #_"map" Compiler'macros
        (array-map
            'about      (λ [& s]   (cons 'do s))
            'declare    (λ [x]     (list 'def x))
            'when       (λ [? & s] (list 'if ? (cons 'do s) nil))
            'cond       (λ [& s]   (when s (list 'if (first s) (second s) (cons 'cond (next (next s))))))
            'and        (λ [& s]   (if s (let [x (first s) s (next s)] (if s (list 'let (list '&and x) (list 'if '&and (cons 'and s) '&and)) x)) true))
            'or         (λ [& s]   (when s (let [x (first s) s (next s)] (if s (list 'let (list '&or x) (list 'if '&or '&or (cons 'or s))) x))))
            '->         (λ [x & s] (loop [x x s s] (if s (recur (let [f (first s)] (if (seq? f) (cons (first f) (cons x (next f))) (list f x))) (next s)) x)))
            'let        (λ [a & s] (if (seq a) (list (list 'λ (list (first a)) (cons 'let (cons (next (next a)) s))) (second a)) (cons 'do s)))
            'loop       (λ [a & s] (cons (cons 'ζ (cons 'recur (cons (Cons''keys a) s))) (Cons''vals a)))
        )
    )

    (def #_"edn" Compiler'macroexpand1 (λ [#_"edn" form, #_"map" scope]
        (if (seq? form)
            (let [#_"fn" f'macro (get Compiler'macros (first form))]
                (if (some? f'macro) (apply f'macro (next form)) form)
            )
            form
        )
    ))

    (def #_"edn" Compiler'macroexpand (λ [#_"edn" form, #_"map" scope]
        (let [#_"edn" me (Compiler'macroexpand1 form, scope)]
            (if (#_= identical? me form) form (#_recur Compiler'macroexpand me, scope))
        )
    ))

    (def #_"void" Compiler'closeOver (λ [#_"Binding" lb, #_"FnExpr" fun]
        (when (and (some? lb) (some? fun) (not (some (λ [%] (#_= identical? % lb)) (get fun :locals))))
            (do
                (swap! (get fun :'closes) (λ [%] (cons lb %)))
                (Compiler'closeOver lb, (get fun :parent))
            )
        )
        nil
    ))

    (def #_"Expr" Compiler'analyzeSymbol (λ [#_"Symbol" sym, #_"map" scope]
        (let [sym (symbol! sym)]
            (or
                (when (= (-/int (-/String''charAt (Symbol''name sym), 0)) Unicode'colon)
                    (LiteralExpr'new sym)
                )
                (when (nil? (Symbol''ns sym))
                    (let [#_"Binding" lb (get (get scope :local-env) sym)]
                        (when (some? lb)
                            (do
                                (Compiler'closeOver lb, (get scope :fun))
                                (BindingExpr'new lb)
                            )
                        )
                    )
                )
                (let [#_"any" o
                        (if (some? (Symbol''ns sym))
                            (-/Namespace''findInternedVar (-/the-ns (-/-symbol "beagle.core")), (-/-symbol (Symbol''name sym)))
                            (get (deref Beagle'ns) sym)
                        )]
                    (if (some? o)
                        (VarExpr'new o)
                        (-/throw! (str "unable to resolve symbol: " sym " in this context"))
                    )
                )
            )
        )
    ))

    (def #_"Expr" Compiler'analyzeSeq (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"edn" me (Compiler'macroexpand1 form, scope)]
            (if (#_= identical? me form)
                (let [#_"any" op (first form)]
                    (if (some? op)
                        (let [#_"fn" f'parse (or (get Compiler'specials op) InvokeExpr'parse)]
                            (f'parse form, context, scope)
                        )
                        (-/throw! (str "can't call nil, form: " form))
                    )
                )
                (Compiler'analyze me, context, scope)
            )
        )
    ))

    (def #_"Expr" Compiler'analyze (λ [#_"edn" form, #_"Context" context, #_"map" scope]
        (cond
            (= form nil)                  LiteralExpr'NIL
            (= form true)                 LiteralExpr'TRUE
            (= form false)                LiteralExpr'FALSE
            (or (symbol? form) (-/-symbol? form)) (Compiler'analyzeSymbol form, scope)
            (and (seq? form) (seq form)) (Compiler'analyzeSeq form, context, scope)
            :else                        (LiteralExpr'new form)
        )
    ))

    (declare Closure'new)

    (def #_"edn" Compiler'eval (λ [#_"edn" form, #_"map" scope]
        (let [form (Compiler'macroexpand form, scope)]
            (apply (Closure'new (Compiler'analyze (list (symbol! 'λ) [] form), :Context'EXPRESSION, scope), nil) nil)
        )
    ))
)

(def eval (λ [form] (Compiler'eval form, nil)))
)

(about #_"beagle.Machine"

(about #_"Machine"
    (def #_"any" Machine'compute (λ [#_"array" code, #_"map" env]
        (loop [#_"stack" s nil #_"int" i 0]
            (let [xy (aget code i) x (first xy) y (second xy)]
                (cond
                    (= x :anew)     (let [a (first s)                          s (next s)]                             (recur (cons (anew a) s)                  (inc i)))
                    (= x :apply)    (let [b (first s) a (second s)             s (next (next s))]                      (recur (cons (apply a (-/-seq b)) s)      (inc i)))
                    (= x :aset)     (let [c (first s) b (second s) a (third s) s (next (next (next s)))] (aset! a b c) (recur s                                  (inc i)))
                    (= x :create)   (let [a (first s)                          s (next s)]                             (recur (cons (Closure'new y, a) s)        (inc i)))
                    (= x :dup)      (let [a (first s)]                                                                 (recur (cons a s)                         (inc i)))
                    (= x :get)                                                                                         (recur (cons (get env y) s)               (inc i))
                    (= x :goto)                                                                                        (recur s                        (deref y))
                    (= x :if-eq?)   (let [b (first s) a (second s)             s (next (next s))]                      (recur s        (if     (= a b) (deref y) (inc i))))
                    (= x :if-nil?)  (let [a (first s)                          s (next s)]                             (recur s        (if  (nil? a)   (deref y) (inc i))))
                    (= x :invoke-1) (let [a (first s)                          s (next s)]                             (recur (cons (y a) s)                     (inc i)))
                    (= x :invoke-2) (let [b (first s) a (second s)             s (next (next s))]                      (recur (cons (y a b) s)                   (inc i)))
                    (= x :pop)                                                                                         (recur (next s)                           (inc i))
                    (= x :push)                                                                                        (recur (cons y s)                         (inc i))
                    (= x :return)   (first s)
                )
            )
        )
    ))
)
)

(about #_"beagle.LispReader"

(about #_"LispReader"
    (declare LispReader'macros)

    (def #_"boolean" LispReader'isMacro (λ [#_"unicode" c]
        (contains? LispReader'macros c)
    ))

    (def #_"boolean" LispReader'isTerminatingMacro (λ [#_"unicode" c]
        (and (LispReader'isMacro c) (not= c Unicode'hash) (not= c Unicode'apostrophe))
    ))

    (def #_"boolean" LispReader'isDigit (λ [#_"unicode" c]
        (and (<= Unicode'0 c) (<= c Unicode'9))
    ))

    (def #_"unicode" LispReader'naught 31)

    (def #_"boolean" LispReader'isWhitespace (λ [#_"unicode" c]
        (or (= c Unicode'space) (= c Unicode'comma) (= c Unicode'newline) (= c LispReader'naught))
    ))

    (def #_"Unicode" LispReader'read1 (λ [#_"Reader" r]
        (let [#_"unicode" c (-/Reader''read r)]
            (when (not= c -1)
                c
            )
        )
    ))

    (def #_"void" LispReader'unread (λ [#_"PushbackReader" r, #_"Unicode" c]
        (when (some? c)
            (-/PushbackReader''unread r, c)
        )
        nil
    ))

    (def #_"Pattern" LispReader'rxInteger (-/Pattern'compile "[-+]?(?:0|[1-9][0-9]*)"))

    (def #_"number" LispReader'matchNumber (λ [#_"String" s]
        (let [#_"Matcher" m (-/Pattern''matcher LispReader'rxInteger, s)]
            (when (-/Matcher''matches m)
                (-/Integer'parseInt s)
            )
        )
    ))

    (def #_"number" LispReader'readNumber (λ [#_"PushbackReader" r, #_"unicode" c]
        (let [#_"String" s
                (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, (-/char c))]
                    (loop []
                        (let [c (LispReader'read1 r)]
                            (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isMacro c))
                                (do
                                    (LispReader'unread r, c)
                                    (-/StringBuilder''toString sb)
                                )
                                (do
                                    (-/StringBuilder''append sb, (-/char c))
                                    (recur)
                                )
                            )
                        )
                    )
                )]
            (or (LispReader'matchNumber s) (-/throw! (str "invalid number: " s)))
        )
    ))

    (def #_"String" LispReader'readToken (λ [#_"PushbackReader" r, #_"unicode" c]
        (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, (-/char c))]
            (loop []
                (let [c (LispReader'read1 r)]
                    (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isTerminatingMacro c))
                        (do
                            (LispReader'unread r, c)
                            (-/StringBuilder''toString sb)
                        )
                        (do
                            (-/StringBuilder''append sb, (-/char c))
                            (recur)
                        )
                    )
                )
            )
        )
    ))

    #_"\n !\"#%&'()*+,-./0123479:;<=>?@ABCDEFGHIKLMNOPRSTUVWXYZ[\\]^_`abcdefghijklmnopqrstuvwxyz{|}~ζλ"

    (def #_"Pattern" LispReader'rxSymbol (-/Pattern'compile "(?:-/)?[-+:a-zA-Z_*?!<=>&%λζ][-+:a-zA-Z_*?!<=>&%0-9'#]*"))

    (def #_"symbol" LispReader'matchSymbol (λ [#_"String" s]
        (let [#_"Matcher" m (-/Pattern''matcher LispReader'rxSymbol, s)]
            (when (-/Matcher''matches m)
                (symbol s)
            )
        )
    ))

    (def #_"symbol" LispReader'interpretToken (λ [#_"String" s]
        (cond (= s "nil") nil (= s "true") true (= s "false") false :else
            (or (LispReader'matchSymbol s) (-/throw! (str "invalid token: " s)))
        )
    ))

    (def #_"any" LispReader'read (λ [#_"PushbackReader" r, #_"map" scope, #_"Unicode" delim, #_"any" delim!]
        (loop []
            (let [#_"Unicode" c (loop [c (LispReader'read1 r)] (if (and (some? c) (LispReader'isWhitespace c)) (recur (LispReader'read1 r)) c))]
                (cond
                    (nil? c)
                        (-/throw! "EOF while reading")
                    (and (some? delim) (= delim c))
                        delim!
                    (LispReader'isDigit c)
                        (LispReader'readNumber r, c)
                    :else
                        (let [#_"fn" f'macro (get LispReader'macros c)]
                            (if (some? f'macro)
                                (let [#_"any" o (f'macro r scope c)]
                                    (if (identical? o r) (recur) o)
                                )
                                (or
                                    (when (or (= c Unicode'plus) (= c Unicode'minus))
                                        (let [#_"Unicode" c' (LispReader'read1 r) _ (LispReader'unread r, c')]
                                            (when (and (some? c') (LispReader'isDigit c'))
                                                (LispReader'readNumber r, c)
                                            )
                                        )
                                    )
                                    (LispReader'interpretToken (LispReader'readToken r, c))
                                )
                            )
                        )
                )
            )
        )
    ))

    (def #_"any" LispReader'READ_FINISHED (anew 0))

    (def #_"seq" LispReader'readDelimitedForms (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" delim]
        (loop [#_"seq" z nil]
            (let [#_"any" form (LispReader'read r, scope, delim, LispReader'READ_FINISHED)]
                (if (identical? form LispReader'READ_FINISHED)
                    (reverse z)
                    (recur (cons form z))
                )
            )
        )
    ))

    (def #_"unicode" StringReader'escape (λ [#_"PushbackReader" r]
        (let [#_"Unicode" c (LispReader'read1 r)]
            (if (some? c)
                (cond
                    (= c Unicode'n)         Unicode'newline
                    (= c Unicode'backslash) c
                    (= c Unicode'quotation) c
                    :else (-/throw! (str "unsupported escape character: \\" (-/char c)))
                )
                (-/throw! "EOF while reading string")
            )
        )
    ))

    (def #_"any" string-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (let [#_"StringBuilder" sb (-/StringBuilder'new)]
            (loop []
                (let [#_"Unicode" c (LispReader'read1 r)]
                    (if (some? c)
                        (when (not= c Unicode'quotation)
                            (do
                                (-/StringBuilder''append sb, (-/char (if (= c Unicode'backslash) (StringReader'escape r) c)))
                                (recur)
                            )
                        )
                        (-/throw! "EOF while reading string")
                    )
                )
            )
            (-/StringBuilder''toString sb)
        )
    ))

    (def #_"any" discard-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (LispReader'read r, scope, nil, nil)
        r
    ))

    (def #_"any" quote-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (list (symbol! 'quote) (LispReader'read r, scope, nil, nil))
    ))

    (declare LispReader'dispatchMacros)

    (def #_"any" dispatch-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (let [#_"Unicode" c (LispReader'read1 r)]
            (if (some? c)
                (let [#_"fn" f'macro (get LispReader'dispatchMacros c)]
                    (if (some? f'macro)
                        (f'macro r scope c)
                        (do
                            (LispReader'unread r, c)
                            (-/throw! (str "no dispatch macro for: " (-/char c)))
                        )
                    )
                )
                (-/throw! "EOF while reading character")
            )
        )
    ))

    (def #_"any" list-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (apply list (LispReader'readDelimitedForms r, scope, Unicode'rparen))
    ))

    (def #_"any" vector-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"unicode" _delim]
        (apply list (LispReader'readDelimitedForms r, scope, Unicode'rbracket))
    ))

    (def #_"any" unmatched-delimiter-reader (λ [#_"PushbackReader" _r, #_"map" scope, #_"unicode" delim]
        (-/throw! (str "unmatched delimiter: " (-/char delim)))
    ))

    (def #_"{unicode fn}" LispReader'macros
        (array-map
            Unicode'quotation   string-reader
            Unicode'apostrophe  quote-reader        Unicode'grave     quote-reader
            Unicode'lparen      list-reader         Unicode'rparen    unmatched-delimiter-reader
            Unicode'lbracket    vector-reader       Unicode'rbracket  unmatched-delimiter-reader
            Unicode'hash        dispatch-reader
        )
    )

    (def #_"{unicode fn}" LispReader'dispatchMacros
        (array-map
            Unicode'underscore  discard-reader
        )
    )
)

(def read (λ [] (LispReader'read -/System'in, nil, nil, nil)))
)

(about #_"Beagle"

(def repl (λ []
    (let [esc (-/char 27)] (print (str esc "[31mBeagle " esc "[32m=> " esc "[0m")))
    (flush)
    (-> (read) (eval) (prn))
    (#_recur repl)
))
)
