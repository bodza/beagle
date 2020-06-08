(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* = aget apply aset char char? class conj defn doseq first fn fn? import int keys let map merge meta neg? next not ns-imports ns-resolve ns-unmap number? object-array select-keys seq seq? seqable? some? str string? symbol symbol? the-ns var? var-get vary-meta when])
    (:require [clojure.core :as -])
)

(-/defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (ns-imports *ns*))] (ns-unmap *ns* n#)) (import ~@syms-or-seqs)))

(import!
    [java.lang Error Integer String]
    [clojure.lang Var]
)

(-/defmacro refer! [ns s]
    (let [f (fn [%] (let [v (ns-resolve (the-ns ns) %) n (vary-meta % merge (select-keys (meta v) [:macro]))] `(def ~n ~(var-get v))))]
        (if (symbol? s) (f s) (-/cons 'do (map f s)))
    )
)

(refer! clojure.core [-> and cond cons defmacro identical? list memoize or time])

(defn throw! [& s] (throw (Error. (apply str s))))

(defn -append [_ x] (.append *out*, x) _)
(defn -flush  [_]   (.flush *out*) _)

(defn -unread [_ c] (.unread *in*, (int c)))
(defn -read   [_]   (let [x (.read *in*)] (when (not (neg? x)) (char x))))

(defn binary [s] (char (Integer/parseInt (if (number? s) (str s) s), 2)))

(defn -var-find [^String s] (.findInternedVar (the-ns 'beagle.core), (symbol s)))
(defn -var-get  [^Var this] (.get this))

(def -=        =)
(def -apply    apply)
(def -char?    char?)
(def -conj     conj)
(def -first    first)
(def -fn?      fn?)
(def -next     next)
(def -seq      seq)
(def -seq?     seq?)
(def -seqable? seqable?)
(def -str      str)
(def -string?  string?)
(def -symbol?  symbol?)
(def -var?     var?)

(defn -aget-0 [a] (aget a 0))
(defn -aget-1 [a] (aget a 1))
(defn -aget-2 [a] (aget a 2))

(defn -anew-0 [] (object-array 0))
(defn -anew-2 [] (object-array 2))
(defn -anew-3 [] (object-array 3))

(defn -array? [x] (and (some? x) (.isArray (class x))))

(defn -aset-0! [a x] (aset a 0 x) a)
(defn -aset-1! [a x] (aset a 1 x) a)
(defn -aset-2! [a x] (aset a 2 x) a)

(defn -volatile-acas-1! [a x y] (when (identical? (-aget-1 a) x) (-aset-1! a y)))
(defn -volatile-aget-1  [a]     (-aget-1 a))
(defn -volatile-aset-1! [a x]   (-aset-1! a x))

(def Atom'meta    (-anew-0))
(def Cons'meta    (-anew-0))
(def String'meta  (-anew-0))
(def Symbol'meta  (-anew-0))
(def Closure'meta (-anew-0))

(ns beagle.core
    (:refer-clojure :only [])
    (:require [beagle.bore :as -])
)

(-/import!)

(-/refer! beagle.bore [-> -= Atom'meta Closure'meta Cons'meta String'meta Symbol'meta -aget-0 -aget-1 -aget-2 and -anew-0 -anew-2 -anew-3 -append -apply -array? -aset-0! -aset-1! -aset-2! binary -char? cond -conj cons -first -flush -fn? identical? list -next or -read -seq -seq? -seqable? -str -string? throw! -unread -var? -var-find -var-get -volatile-acas-1! -volatile-aget-1 -volatile-aset-1!])

(-/defmacro about   [& s]   (-/cons 'do s))
(-/defmacro declare [x]     (-/list 'def x nil))
(-/defmacro when    [? & s] (-/list 'if ? (-/cons 'do s) nil))

(-/defmacro fn   [& s] (-/cons 'fn* s))
(-/defmacro let  [& s] (-/cons 'let* s))
(-/defmacro loop [& s] (-/cons 'loop* s))

(-/defmacro defn     [f & s] (-/list 'def f (-/cons 'fn s)))
(-/defmacro lazy-seq [& s]   (-/cons 'fn (-/cons [] s)))

(-/defmacro &do [& s] (-/cons 'do s))

(def &binary     -/binary)
(def &identical? -/identical?)
(def &throw!     -/throw!)

(about #_"Beagle")

(defn memoize  [x] x)
(defn -symbol? [x] false)

(defn identical? [x y] (&identical? x y))

(defn identity [x] x)

(defn nil?   [x] (identical? x nil))
(defn true?  [x] (identical? x true))
(defn false? [x] (identical? x false))
(defn not    [x] (if x false true))
(defn some?  [x] (not (nil? x)))

(about #_"seq"
    (declare cons?)
    (declare Cons''seq)
    (declare string?)
    (declare String''seq)
    (declare closure?)
    (declare Closure''seq)

    (defn seq [s]
        (cond
            (nil? s)         nil
            (cons? s)       (Cons''seq s)
            (string? s)     (String''seq s)
            (closure? s)    (Closure''seq s)
            (-/-seqable? s) (-/-seq s)
            (-/-fn? s)      (-/-apply s nil)
            'else           (&throw! "seq not supported on " s)
        )
    )

    (declare Cons''first)

    (defn first [s]
        (let [s (seq s)]
            (cond
                (nil? s)     nil
                (cons? s)   (Cons''first s)
                (-/-seq? s) (-/-first s)
                'else       (&throw! "first not supported on " s)
            )
        )
    )

    (declare Cons''next)

    (defn next [s]
        (let [s (seq s)]
            (cond
                (nil? s)     nil
                (cons? s)   (Cons''next s)
                (-/-seq? s) (-/-next s)
                'else       (&throw! "next not supported on " s)
            )
        )
    )

    (defn second [s] (first (next s)))
    (defn third  [s] (first (next (next s))))
    (defn fourth [s] (first (next (next (next s)))))
    (defn fifth  [s] (first (next (next (next (next s))))))

    (defn last [s] (let [r (next s)] (if (some? r) (#_recur last r) (first s))))

    (defn reduce [f r s] (let [s (seq s)] (if (some? s) (#_recur reduce f (f r (first s)) (next s)) r)))

    (defn reduce-kv [f r kvs] (let [kvs (seq kvs)] (if (some? kvs) (#_recur reduce-kv f (f r (first kvs) (second kvs)) (next (next kvs))) r)))
)

(about #_"Atom"
    (defn Atom'new [init]
        (-> (-/-anew-2) (-/-aset-0! -/Atom'meta) (-/-volatile-aset-1! init))
    )

    (declare =)

    (defn atom? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) -/Atom'meta)))

    (defn Atom''deref [this]
        (-/-volatile-aget-1 this)
    )

    (declare apply)

    (defn Atom''swap [this, f, s]
        (loop []
            (let [o (-/-volatile-aget-1 this) o' (apply f o s)]
                (if (-/-volatile-acas-1! this o o') o' (recur))
            )
        )
    )

    (defn Atom''reset [this, o']
        (-/-volatile-aset-1! this o')
        o'
    )
)

(defn atom [x] (Atom'new x))

(defn deref [a]
    (cond
        (atom? a) (Atom''deref a)
        'else     (&throw! "deref not supported on " a)
    )
)

(defn swap! [a f & s]
    (cond
        (atom? a) (Atom''swap a, f, s)
        'else     (&throw! "swap! not supported on " a)
    )
)

(defn reset! [a x]
    (cond
        (atom? a) (Atom''reset a, x)
        'else     (&throw! "reset! not supported on " a)
    )
)

(about #_"Cons"
    (defn Cons'new [car, cdr]
        (-> (-/-anew-3) (-/-aset-0! -/Cons'meta) (-/-aset-1! car) (-/-aset-2! cdr))
    )

    (defn cons? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) -/Cons'meta)))

    (defn Cons''car [this] (when (cons? this) (-/-aget-1 this)))
    (defn Cons''cdr [this] (when (cons? this) (-/-aget-2 this)))

    (defn Cons''seq [this]
        this
    )

    (defn Cons''first [this]      (Cons''car this))
    (defn Cons''next  [this] (seq (Cons''cdr this)))

    (defn Cons''equals [this, that]
        (or (identical? this that)
            (and (or (cons? that) (-/-seqable? that))
                (loop [s (seq this) z (seq that)]
                    (if (some? s)
                        (and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                        (nil? z)
                    )
                )
            )
        )
    )
)

(defn cons [x s] (Cons'new x, (#_seq identity s)))

(defn conj [s x] (cons x s))

(defn spread [s]
    (cond
        (nil? s)         nil
        (nil? (next s)) (seq (first s))
        'else           (cons (first s) (spread (next s)))
    )
)

(defn reverse [s] (reduce conj nil s))

(defn list [& s] s)

(defn some [f s]
    (let [s (seq s)]
        (when (some? s)
            (or (f (first s)) (#_recur some f (next s)))
        )
    )
)

(defn some-kv [f kvs]
    (let [kvs (seq kvs)]
        (when (some? kvs)
            (or (f kvs) (#_recur some-kv f (next (next kvs))))
        )
    )
)

(defn map [f s]
    (lazy-seq
        (let [s (seq s)]
            (when (some? s)
                (cons (f (first s)) (map f (next s)))
            )
        )
    )
)

(about #_"ConsMap"
    (defn ConsMap'new [car, cadr, cddr]
        (cons car (cons cadr cddr))
    )

    (defn ConsMap''find [this, key]
        (some-kv (fn [e] (when (= (first e) key) e)) this)
    )

    (defn ConsMap''contains? [this, key]
        (some? (ConsMap''find this, key))
    )

    (defn ConsMap''get [this, key]
        (second (ConsMap''find this, key))
    )

    (defn ConsMap''assoc [this, key, val]
        (if (and (#_= identical? (first this) key) (#_= identical? (second this) val))
            this
            (ConsMap'new key, val, this)
        )
    )

    (defn ConsMap''keys [this]
        (lazy-seq
            (let [s (seq this)]
                (when (some? s)
                    (cons (first s) (ConsMap''keys (next (next s))))
                )
            )
        )
    )

    (defn ConsMap''vals [this]
        (lazy-seq
            (let [s (seq this)]
                (when (some? s)
                    (cons (second s) (ConsMap''vals (next (next s))))
                )
            )
        )
    )
)

(defn assoc [m k v]
    (cond
        (nil? m)  (ConsMap'new k, v, nil)
        (cons? m) (ConsMap''assoc m, k, v)
        'else     (&throw! "assoc not supported on " m)
    )
)

(defn cons-map [& kvs] (reduce-kv assoc nil kvs))

(defn contains? [m k]
    (cond
        (nil? m)   false
        (cons? m) (ConsMap''contains? m, k)
        'else     (&throw! "contains? not supported on " m)
    )
)

(defn get [m k]
    (cond
        (nil? m)   nil
        (cons? m) (ConsMap''get m, k)
        'else     (&throw! "get not supported on " m)
    )
)

(defn update [m k f & s] (assoc m k (apply f (get m k) s)))

(about #_"String"
    (defn String'new [s]
        (-> (-/-anew-2) (-/-aset-0! -/String'meta) (-/-aset-1! s))
    )

    (defn string? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) -/String'meta)))

    (defn String''s [this] (when (string? this) (-/-aget-1 this)))

    (defn String''seq [this] (seq (String''s this)))

    (defn String''equals [this, that]
        (or (identical? this that)
            (and (or (string? that) (-/-string? that))
                (loop [s (seq this) z (seq that)]
                    (if (some? s)
                        (and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                        (nil? z)
                    )
                )
            )
        )
    )
)

(defn string [s] (cond (string? s) s (-/-string? s) (String'new s) 'else (String'new (-/-str s))))

(about #_"Symbol"
    (defn Symbol'new [name, alt?]
        (-> (-/-anew-3) (-/-aset-0! -/Symbol'meta) (-/-aset-1! name) (-/-aset-2! alt?))
    )

    (defn symbol? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) -/Symbol'meta)))

    (defn Symbol''name [this] (when (symbol? this) (-/-aget-1 this)))
    (defn Symbol''alt? [this] (when (symbol? this) (-/-aget-2 this)))

    (declare Unicode'minus)
    (declare Unicode'slash)

    (defn Symbol'create [s]
        (let [
            alt? (and (= (first s) Unicode'minus) (= (second s) Unicode'slash))
        ]
            (Symbol'new (string (if alt? (next (next s)) s)), alt?)
        )
    )

    (def Symbol'create (-/memoize Symbol'create))

    (defn Symbol''equals [this, that]
        (or (identical? this that)
            (and (symbol? that)
                (= (Symbol''alt? this) (Symbol''alt? that))
                (= (Symbol''name this) (Symbol''name that))
            )
        )
    )
)

(defn symbol! [s] (if (-/-symbol? s) (Symbol'create (-/-str s)) s))

(defn symbol [s] (cond (symbol? s) s (-/-symbol? s) (Symbol'create (-/-str s)) 'else (Symbol'create s)))

(about #_"unicode"
    (defn binary [s] (&binary s))

    (def Unicode'newline     (binary    '1010))
    (def Unicode'escape      (binary   '11011))
    (def Unicode'space       (binary  '100000))
    (def Unicode'exclamation (binary  '100001))
    (def Unicode'quotation   (binary  '100010))
    (def Unicode'hash        (binary  '100011))
    (def Unicode'percent     (binary  '100101))
    (def Unicode'ampersand   (binary  '100110))
    (def Unicode'apostrophe  (binary  '100111))
    (def Unicode'lparen      (binary  '101000))
    (def Unicode'rparen      (binary  '101001))
    (def Unicode'asterisk    (binary  '101010))
    (def Unicode'comma       (binary  '101100))
    (def Unicode'minus       (binary  '101101))
    (def Unicode'slash       (binary  '101111))
    (def Unicode'0           (binary  '110000))
    (def Unicode'1           (binary  '110001))
    (def Unicode'2           (binary  '110010))
    (def Unicode'3           (binary  '110011))
    (def Unicode'4           (binary  '110100))
    (def Unicode'5           (binary  '110101))
    (def Unicode'6           (binary  '110110))
    (def Unicode'7           (binary  '110111))
    (def Unicode'8           (binary  '111000))
    (def Unicode'9           (binary  '111001))
    (def Unicode'equals      (binary  '111101))
    (def Unicode'greater     (binary  '111110))
    (def Unicode'question    (binary  '111111))
    (def Unicode'A           (binary '1000001))
    (def Unicode'B           (binary '1000010))
    (def Unicode'C           (binary '1000011))
    (def Unicode'D           (binary '1000100))
    (def Unicode'E           (binary '1000101))
    (def Unicode'F           (binary '1000110))
    (def Unicode'G           (binary '1000111))
    (def Unicode'H           (binary '1001000))
    (def Unicode'I           (binary '1001001))
    (def Unicode'J           (binary '1001010))
    (def Unicode'K           (binary '1001011))
    (def Unicode'L           (binary '1001100))
    (def Unicode'M           (binary '1001101))
    (def Unicode'N           (binary '1001110))
    (def Unicode'O           (binary '1001111))
    (def Unicode'P           (binary '1010000))
    (def Unicode'Q           (binary '1010001))
    (def Unicode'R           (binary '1010010))
    (def Unicode'S           (binary '1010011))
    (def Unicode'T           (binary '1010100))
    (def Unicode'U           (binary '1010101))
    (def Unicode'V           (binary '1010110))
    (def Unicode'W           (binary '1010111))
    (def Unicode'X           (binary '1011000))
    (def Unicode'Y           (binary '1011001))
    (def Unicode'Z           (binary '1011010))
    (def Unicode'lbracket    (binary '1011011))
    (def Unicode'backslash   (binary '1011100))
    (def Unicode'rbracket    (binary '1011101))
    (def Unicode'underscore  (binary '1011111))
    (def Unicode'grave       (binary '1100000))
    (def Unicode'a           (binary '1100001))
    (def Unicode'b           (binary '1100010))
    (def Unicode'c           (binary '1100011))
    (def Unicode'd           (binary '1100100))
    (def Unicode'e           (binary '1100101))
    (def Unicode'f           (binary '1100110))
    (def Unicode'g           (binary '1100111))
    (def Unicode'h           (binary '1101000))
    (def Unicode'i           (binary '1101001))
    (def Unicode'j           (binary '1101010))
    (def Unicode'k           (binary '1101011))
    (def Unicode'l           (binary '1101100))
    (def Unicode'm           (binary '1101101))
    (def Unicode'n           (binary '1101110))
    (def Unicode'o           (binary '1101111))
    (def Unicode'p           (binary '1110000))
    (def Unicode'q           (binary '1110001))
    (def Unicode'r           (binary '1110010))
    (def Unicode's           (binary '1110011))
    (def Unicode't           (binary '1110100))
    (def Unicode'u           (binary '1110101))
    (def Unicode'v           (binary '1110110))
    (def Unicode'w           (binary '1110111))
    (def Unicode'x           (binary '1111000))
    (def Unicode'y           (binary '1111001))
    (def Unicode'z           (binary '1111010))
)

(about #_"Closure"
    (defn Closure'new [fun, env]
        (-> (-/-anew-3) (-/-aset-0! -/Closure'meta) (-/-aset-1! fun) (-/-aset-2! env))
    )

    (defn closure? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) -/Closure'meta)))

    (defn Closure''fun [this] (when (closure? this) (-/-aget-1 this)))
    (defn Closure''env [this] (when (closure? this) (-/-aget-2 this)))

    (declare Machine'compute)

    (defn Closure''applyTo [this, args]
        (let [
            fun (Closure''fun this) env (Closure''env this)
            env
                (let [x (second fun)]
                    (if (some? x) (assoc env x this) env)
                )
            env
                (loop [env env pars (seq (third fun)) args (seq args)]
                    (if (some? pars)
                        (recur (assoc env (first pars) (first args)) (next pars) (next args))
                        (let [x (fourth fun)]
                            (if (some? x) (assoc env x args) env)
                        )
                    )
                )
        ]
            (Machine'compute (fifth fun), env)
        )
    )

    (defn Closure''seq [this]
        (Closure''applyTo this, nil)
    )
)

(defn apply [f & s]
    (let [s (spread s)]
        (cond
            (closure? f) (Closure''applyTo f, s)
            (atom? f)    (apply (deref f) s)
            (-/-fn? f)   (-/-apply f (reduce -/-conj (-/list) (reverse s)))
            'else        (&throw! "apply not supported on " f)
        )
    )
)

(about #_"Var"
    (def Beagle'ns (atom nil))

    (defn Var'new []
        (atom nil)
    )

    (defn Var'find [sym]
        (if (not (Symbol''alt? sym))
            (get (deref Beagle'ns) sym)
            (-/-var-find (apply -/-str (Symbol''name sym)))
        )
    )

    (defn Var'lookup [sym]
        (if (not (Symbol''alt? sym))
            (or
                (get (deref Beagle'ns) sym)
                (let [v (Var'new)]
                    (swap! Beagle'ns assoc sym v)
                    v
                )
            )
            (&throw! "can't create defs for alt ns")
        )
    )

    (defn Var''get [this]
        (if (-/-var? this) (-/-var-get this) (deref this))
    )

    (defn Var''set [this, root]
        (reset! this root)
        nil
    )
)

(defn = [x y]
    (cond
        (identical? x y) true
        (or (nil? x) (nil? y) (true? x) (true? y) (false? x) (false? y)) false
        (-/-char? x)     (-/-= x y)
        (symbol? x)      (Symbol''equals x, (symbol! y))
        (symbol? y)      (Symbol''equals y, (symbol! x))
        (-/-symbol? x)   (-/-= x y)
        (string? x)      (String''equals x, y)
        (string? y)      (String''equals y, x)
        (-/-string? x)   (-/-= x y)
        (cons? x)        (Cons''equals x, y)
        (cons? y)        (Cons''equals y, x)
        'else            (&throw! "= not supported on " x ", not even on " y)
    )
)

(about #_"append"
    (def Beagle'in  nil)
    (def Beagle'out nil)

    (defn append' [a x]
        (cond
            (nil? a)                        (-/-append a (if (string? x) (apply -/-str x) x))
            (-/-char? x)                    (conj a x)
            (or (string? x) (-/-string? x)) (reduce conj a x)
            'else                           (&throw! "append' not supported for " x)
        )
    )

    (defn escape-str [c]
        (cond
            (= c Unicode'newline)   "\\n"
            (= c Unicode'quotation) "\\\""
            (= c Unicode'backslash) "\\\\"
            'else                   c
        )
    )

    (defn append-str [a x]
        (let [
            a (append' a "\"")
            a (reduce (fn [%1 %2] (append' %1 (escape-str %2))) a x)
            a (append' a "\"")
        ]
            a
        )
    )

    (defn append-sym [a x]
        (let [
            a (if (Symbol''alt? x) (append' a "-/") a)
            a (append' a (Symbol''name x))
        ]
            a
        )
    )

    (defn append* [a b f'append c d q]
        (let [
            a (append' a b)
            a
                (let [s (seq q)]
                    (if (some? s)
                        (loop [a a s s]
                            (let [a (f'append a (first s)) s (next s)]
                                (if (some? s) (recur (append' a c) s) a)
                            )
                        )
                        a
                    )
                )
            a (append' a d)
        ]
            a
        )
    )

    (declare append)

    (defn append-seq [a x] (append* a "(" append " " ")" x))

    (defn append [a x]
        (cond
            (nil? x)       (append' a "nil")
            (true? x)      (append' a "true")
            (false? x)     (append' a "false")
            (symbol? x)    (append-sym a x)
            (string? x)    (append-str a x)
            (cons? x)      (append-seq a x)
            (atom? x)      (append' a "atom")
            (closure? x)   (append' a "closure")
            (-/-symbol? x) (append-sym a (symbol! x))
            (-/-string? x) (append-str a x)
            (-/-seq? x)    (append' a "-seq")
            (-/-fn? x)     (append' a "-fn")
            'else          (&throw! "append not supported on " x)
        )
    )

    (defn append! [a x]
        (if (or (string? x) (-/-string? x) (-/-char? x)) (append' a x) (append a x))
    )

    (defn str [& s]
        (loop [sb nil s s]
            (if (some? s)
                (let [x (first s)]
                    (recur (if (some? x) (append! sb x) sb) (next s))
                )
                (String'new (reverse sb))
            )
        )
    )

    (defn space   [] (append' Beagle'out Unicode'space)   nil)
    (defn newline [] (append' Beagle'out Unicode'newline) nil)

    (defn flush [] (-/-flush Beagle'out) nil)

    (defn pr [& s]
        (when (some? s)
            (loop [x (first s) s (next s)]
                (append Beagle'out x)
                (when (some? s)
                    (space)
                    (recur (first s) (next s))
                )
            )
        )
        nil
    )

    (defn print [& s]
        (when (some? s)
            (loop [x (first s) s (next s)]
                (append! Beagle'out x)
                (when (some? s)
                    (space)
                    (recur (first s) (next s))
                )
            )
        )
        nil
    )

    (defn prn     [& s] (apply pr    s) (newline) (flush) nil)
    (defn println [& s] (apply print s) (newline) (flush) nil)
)

(about #_"LiteralExpr"
    (def LiteralExpr'NIL   (list '&literal nil))
    (def LiteralExpr'TRUE  (list '&literal true))
    (def LiteralExpr'FALSE (list '&literal false))

    (defn LiteralExpr'parse [form, scope]
        (cond
            (nil? (next form))         (&throw! "too few arguments to quote")
            (some? (next (next form))) (&throw! "too many arguments to quote")
        )
        (let [x (second form)]
            (cond
                (nil? x)    LiteralExpr'NIL
                (true? x)   LiteralExpr'TRUE
                (false? x)  LiteralExpr'FALSE
                'else      (list '&literal x)
            )
        )
    )
)

(about #_"IfExpr"
    (declare Compiler'analyze)

    (defn IfExpr'parse [form, scope]
        (cond
            (nil? (next (next (next form))))         (&throw! "too few arguments to if")
            (some? (next (next (next (next form))))) (&throw! "too many arguments to if")
        )
        (let [
            test (Compiler'analyze (second form), scope)
            then (Compiler'analyze (third form), scope)
            else (Compiler'analyze (fourth form), scope)
        ]
            (list '&if test then else)
        )
    )
)

(about #_"EmbedExpr"
    (defn EmbedExpr'parse [form, scope]
        (let [
            args (map (fn [%] (Compiler'analyze %, scope)) (next form))
        ]
            (cons (first form) args)
        )
    )
)

(about #_"InvokeExpr"
    (defn InvokeExpr'parse [form, scope]
        (let [
            fexpr (Compiler'analyze (first form), scope)
            args (map (fn [%] (Compiler'analyze %, scope)) (next form))
        ]
            (list '&invoke fexpr args)
        )
    )
)

(about #_"FnExpr"
    (defn FnExpr'parse [form, scope]
        (let [
            self (symbol! (second form)) ? (symbol? self) self (when ? self) form (if ? (next (next form)) (next form))
            _
                (loop [pars nil etal nil variadic? false s (seq (first form))]
                    (if (some? s)
                        (let [sym (symbol! (first s))]
                            (if (symbol? sym)
                                (if (not (Symbol''alt? sym))
                                    (cond
                                        (= sym '&)
                                            (if (not variadic?)
                                                (recur pars etal true (next s))
                                                (&throw! "overkill variadic parameter list")
                                            )
                                        (some? etal)
                                            (&throw! "excess variadic parameter " sym)
                                        'else
                                            (if (not variadic?)
                                                (recur (cons sym pars) etal variadic? (next s))
                                                (recur           pars  sym  variadic? (next s))
                                            )
                                    )
                                    (&throw! "can't use alt name as parameter " sym)
                                )
                                (&throw! "function parameters must be symbols")
                            )
                        )
                        (if (or (not variadic?) (some? etal))
                            (list (reverse pars) etal)
                            (&throw! "missing variadic parameter")
                        )
                    )
                )
            pars (first _) etal (second _)
            scope
                (loop [scope (if (some? self) (cons self scope) scope) s (seq pars)]
                    (if (some? s)
                        (recur (cons (first s) scope) (next s))
                        (if (some? etal) (cons etal scope) scope)
                    )
                )
            body (EmbedExpr'parse (cons '&do (next form)), scope)
        ]
            (list '&fn self pars etal body)
        )
    )
)

(about #_"DefExpr"
    (defn DefExpr'parse [form, scope]
        (cond
            (nil? (next (next form)))         (&throw! "too few arguments to def")
            (some? (next (next (next form)))) (&throw! "too many arguments to def")
        )
        (let [s (symbol! (second form))]
            (if (symbol? s)
                (list '&var-set! (Var'lookup s) (Compiler'analyze (third form), scope))
                (&throw! "first argument to def must be a symbol")
            )
        )
    )
)

(about #_"Compiler"
    (def Compiler'specials
        (cons-map
            'def        DefExpr'parse
            'fn         FnExpr'parse
            'if         IfExpr'parse
            'quote      LiteralExpr'parse
        )
    )

    (defn Compiler'embed? [f]
        (or (= f '&do) (= f '&binary) (= f '&identical?) (= f '&throw!))
    )

    (def Compiler'macros
        (cons-map
            'about      (fn [& s]   (cons '&do s))
            'declare    (fn [x]     (list 'def x nil))
            'when       (fn [? & s] (list 'if ? (cons '&do s) nil))
            'cond       (fn [& s]   (when s (list 'if (first s) (second s) (cons 'cond (next (next s))))))
            'and        (fn [& s]   (if s (let [x (first s) s (next s)] (if s (list 'let (list '&and x) (list 'if '&and (cons 'and s) '&and)) x)) true))
            'or         (fn [& s]   (when s (let [x (first s) s (next s)] (if s (list 'let (list '&or x) (list 'if '&or '&or (cons 'or s))) x))))
            '->         (fn [x & s] (loop [x x s s] (if s (recur (let [f (first s)] (if (or (cons? f) (-/-seq? f)) (cons (first f) (cons x (next f))) (list f x))) (next s)) x)))
            'let        (fn [a & s] (if (seq a) (list (list 'fn (list (first a)) (cons 'let (cons (next (next a)) s))) (second a)) (cons '&do s)))
            'loop       (fn [a & s] (cons (cons 'fn (cons 'recur (cons (ConsMap''keys a) s))) (ConsMap''vals a)))
            'defn       (fn [f & s] (list 'def f (cons 'fn s)))
            'lazy-seq   (fn [& s]   (cons 'fn (cons [] s)))
        )
    )

    (defn Compiler'macroexpand1 [form]
        (if (or (cons? form) (-/-seq? form))
            (let [f'macro (get Compiler'macros (first form))]
                (if (some? f'macro) (apply f'macro (next form)) form)
            )
            form
        )
    )

    (defn Compiler'macroexpand [form]
        (let [me (Compiler'macroexpand1 form)]
            (if (#_= identical? me form) form (#_recur Compiler'macroexpand me))
        )
    )

    (defn Compiler'analyzeSymbol [sym, scope]
        (or
            (when (and (not (Symbol''alt? sym)) (some (fn [%] (= % sym)) scope))
                (list '&binding sym)
            )
            (let [v (Var'find sym)]
                (when (some? v)
                    (list '&var-get v)
                )
            )
            (&throw! "unable to resolve symbol " sym)
        )
    )

    (defn Compiler'analyzeSeq [form, scope]
        (let [me (Compiler'macroexpand1 form)]
            (if (#_= identical? me form)
                (let [op (first form)]
                    (if (some? op)
                        (let [f'parse (or (get Compiler'specials op) (if (Compiler'embed? op) EmbedExpr'parse InvokeExpr'parse))]
                            (f'parse form scope)
                        )
                        (&throw! "can't call nil in form " form)
                    )
                )
                (Compiler'analyze me, scope)
            )
        )
    )

    (defn Compiler'analyze [form, scope]
        (cond
            (nil? form)                                           LiteralExpr'NIL
            (true? form)                                          LiteralExpr'TRUE
            (false? form)                                         LiteralExpr'FALSE
            (or (symbol? form) (-/-symbol? form))                (Compiler'analyzeSymbol (symbol! form), scope)
            (or (cons? form) (and (-/-seq? form) (-/-seq form))) (Compiler'analyzeSeq form, scope)
            'else                                                (list '&literal form)
        )
    )

    (defn Compiler'eval [form]
        (let [form (Compiler'macroexpand form)]
            (apply (Closure'new (Compiler'analyze (list 'fn [] form), nil), nil) nil)
        )
    )
)

(defn eval [form] (Compiler'eval form))

(about #_"machine"
    (defn Machine'compute [form, env]
        (let [f (first form) f'compute (fn [%] (Machine'compute %, env))]
            (cond
                (= f '&literal)    (second form)
                (= f '&binding)    (get env (second form))
                (= f '&var-get)    (Var''get (second form))
                (= f '&if)         (f'compute (if (f'compute (second form)) (third form) (fourth form)))
                (= f '&invoke)     (apply (f'compute (second form)) (map f'compute (third form)))
                (= f '&do)         (last (map f'compute (next form)))
                (= f '&fn)         (Closure'new form, env)
                (= f '&var-set!)   (Var''set (second form), (f'compute (third form)))
                (= f '&binary)     (-/binary (apply -/-str (Symbol''name (f'compute (second form)))))
                (= f '&identical?) (-/identical? (f'compute (second form)) (f'compute (third form)))
                (= f '&throw!)     (apply -/throw! (map (fn [%] (apply -/-str %)) (map f'compute (next form))))
                'else              (&throw! "Machine'compute not supported on " form)
            )
        )
    )
)

(about #_"LispReader"
    (declare LispReader'macros)

    (defn LispReader'isMacro [c]
        (some? (get LispReader'macros c))
    )

    (defn LispReader'isTerminatingMacro [c]
        (and (LispReader'isMacro c) (not (= c Unicode'hash)) (not (= c Unicode'apostrophe)))
    )

    (defn LispReader'isLetter [c]
        (or
            (= c Unicode'a) (= c Unicode'A)
            (= c Unicode'b) (= c Unicode'B)
            (= c Unicode'c) (= c Unicode'C)
            (= c Unicode'd) (= c Unicode'D)
            (= c Unicode'e) (= c Unicode'E)
            (= c Unicode'f) (= c Unicode'F)
            (= c Unicode'g) (= c Unicode'G)
            (= c Unicode'h) (= c Unicode'H)
            (= c Unicode'i) (= c Unicode'I)
            (= c Unicode'j) (= c Unicode'J)
            (= c Unicode'k) (= c Unicode'K)
            (= c Unicode'l) (= c Unicode'L)
            (= c Unicode'm) (= c Unicode'M)
            (= c Unicode'n) (= c Unicode'N)
            (= c Unicode'o) (= c Unicode'O)
            (= c Unicode'p) (= c Unicode'P)
            (= c Unicode'q) (= c Unicode'Q)
            (= c Unicode'r) (= c Unicode'R)
            (= c Unicode's) (= c Unicode'S)
            (= c Unicode't) (= c Unicode'T)
            (= c Unicode'u) (= c Unicode'U)
            (= c Unicode'v) (= c Unicode'V)
            (= c Unicode'w) (= c Unicode'W)
            (= c Unicode'x) (= c Unicode'X)
            (= c Unicode'y) (= c Unicode'Y)
            (= c Unicode'z) (= c Unicode'Z)
        )
    )

    (defn LispReader'isDigit [c]
        (or (= c Unicode'0) (= c Unicode'1) (= c Unicode'2) (= c Unicode'3) (= c Unicode'4) (= c Unicode'5) (= c Unicode'6) (= c Unicode'7) (= c Unicode'8) (= c Unicode'9))
    )

    (def LispReader'naught (binary '11111))

    (defn LispReader'isWhitespace [c]
        (or (= c Unicode'space) (= c Unicode'comma) (= c Unicode'newline) (= c LispReader'naught))
    )

    (defn LispReader'read1 [r]
        (-/-read r)
    )

    (defn LispReader'unread [r, c]
        (when (some? c)
            (-/-unread r c)
        )
        nil
    )

    (defn LispReader'readToken [r, c]
        (loop [s (cons c nil)]
            (let [c (LispReader'read1 r)]
                (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isTerminatingMacro c))
                    (&do
                        (LispReader'unread r, c)
                        (String'new (reverse s))
                    )
                    (recur (cons c s))
                )
            )
        )
    )

    #_"\n !\"#%&'()*,-./0123456789=>?ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]_abcdefghijklmnopqrstuvwxyz"

    (defn LispReader'isSymbol [s]
        (let [s (if (and (= (first s) Unicode'minus) (= (second s) Unicode'slash)) (next (next s)) s)]
            (and
                (let [c (first s)]
                    (or (= c Unicode'minus) (LispReader'isLetter c) (= c Unicode'underscore) (LispReader'isDigit c) (= c Unicode'question) (= c Unicode'exclamation) (= c Unicode'equals) (= c Unicode'ampersand) (= c Unicode'percent))
                )
                (loop [s (next s)]
                    (or (nil? s)
                        (and
                            (let [c (first s)]
                                (or (= c Unicode'minus) (LispReader'isLetter c) (= c Unicode'underscore) (LispReader'isDigit c) (= c Unicode'apostrophe) (= c Unicode'asterisk) (= c Unicode'question) (= c Unicode'exclamation) (= c Unicode'equals) (= c Unicode'greater))
                            )
                            (recur (next s))
                        )
                    )
                )
            )
        )
    )

    (defn LispReader'interpretToken [s]
        (cond
            (= s "nil")              nil
            (= s "true")             true
            (= s "false")            false
            (LispReader'isSymbol s) (symbol s)
            'else                   (&throw! "invalid token " s)
        )
    )

    (defn LispReader'read [r, scope, delim, delim!]
        (loop []
            (let [c (loop [c (LispReader'read1 r)] (if (and (some? c) (LispReader'isWhitespace c)) (recur (LispReader'read1 r)) c))]
                (cond
                    (nil? c)
                        (&throw! "EOF while reading")
                    (and (some? delim) (= delim c))
                        delim!
                    'else
                        (let [f'macro (get LispReader'macros c)]
                            (if (some? f'macro)
                                (let [o (f'macro r scope c)]
                                    (if (identical? o r) (recur) o)
                                )
                                (LispReader'interpretToken (LispReader'readToken r, c))
                            )
                        )
                )
            )
        )
    )

    (def LispReader'READ_FINISHED (-/-anew-0))

    (defn LispReader'readDelimitedForms [r, scope, delim]
        (loop [z nil]
            (let [form (LispReader'read r, scope, delim, LispReader'READ_FINISHED)]
                (if (identical? form LispReader'READ_FINISHED)
                    (reverse z)
                    (recur (cons form z))
                )
            )
        )
    )

    (defn StringReader'escape [r]
        (let [c (LispReader'read1 r)]
            (if (some? c)
                (cond
                    (= c Unicode'n)         Unicode'newline
                    (= c Unicode'backslash) c
                    (= c Unicode'quotation) c
                    'else                   (&throw! "unsupported escape character \\" c)
                )
                (&throw! "EOF while reading string")
            )
        )
    )

    (defn string-reader [r, scope, _delim]
        (loop [s nil]
            (let [c (LispReader'read1 r)]
                (if (some? c)
                    (if (= c Unicode'quotation)
                        (String'new (reverse s))
                        (recur (cons (if (= c Unicode'backslash) (StringReader'escape r) c) s))
                    )
                    (&throw! "EOF while reading string")
                )
            )
        )
    )

    (defn discard-reader [r, scope, _delim]
        (LispReader'read r, scope, nil, nil)
        r
    )

    (defn quote-reader [r, scope, _delim]
        (list 'quote (LispReader'read r, scope, nil, nil))
    )

    (declare LispReader'dispatchMacros)

    (defn dispatch-reader [r, scope, _delim]
        (let [c (LispReader'read1 r)]
            (if (some? c)
                (let [f'macro (get LispReader'dispatchMacros c)]
                    (if (some? f'macro)
                        (f'macro r scope c)
                        (&do
                            (LispReader'unread r, c)
                            (&throw! "no dispatch macro for " c)
                        )
                    )
                )
                (&throw! "EOF while reading character")
            )
        )
    )

    (defn list-reader [r, scope, _delim]
        (LispReader'readDelimitedForms r, scope, Unicode'rparen)
    )

    (defn vector-reader [r, scope, _delim]
        (LispReader'readDelimitedForms r, scope, Unicode'rbracket)
    )

    (defn unmatched-delimiter-reader [_r, scope, delim]
        (&throw! "unmatched delimiter " delim)
    )

    (def LispReader'macros
        (cons-map
            Unicode'quotation   string-reader
            Unicode'apostrophe  quote-reader        Unicode'grave     quote-reader
            Unicode'lparen      list-reader         Unicode'rparen    unmatched-delimiter-reader
            Unicode'lbracket    vector-reader       Unicode'rbracket  unmatched-delimiter-reader
            Unicode'hash        dispatch-reader
        )
    )

    (def LispReader'dispatchMacros
        (cons-map
            Unicode'underscore  discard-reader
        )
    )
)

(defn read [] (LispReader'read Beagle'in, nil, nil, nil))

(defn repl []
    (let [esc Unicode'escape] (print (str esc "[31mBeagle " esc "[32m=> " esc "[0m")))
    (flush)
    (-> (read) (eval) (prn))
    (#_recur repl)
)

#_(repl)
