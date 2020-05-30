(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* = aget alength apply aset boolean? char char? class conj defn doseq first fn fn? import inc int keys let map merge meta name namespace neg? next ns-imports ns-resolve ns-unmap number? object-array select-keys seq seq? seqable? some? str string? symbol symbol? the-ns var? var-get vary-meta])
    (:require [clojure.core :as -])
)

(-/defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (ns-imports *ns*))] (ns-unmap *ns* n#)) (import ~@syms-or-seqs)))

(import!
    [java.lang Appendable Error Integer StringBuilder]
    [java.io Flushable PrintWriter PushbackReader Reader]
    [java.util.regex Matcher Pattern]
    [clojure.lang Namespace Var]
)

(-/defmacro refer! [ns s]
    (let [f (fn [%] (let [v (ns-resolve (the-ns ns) %) n (vary-meta % merge (select-keys (meta v) [:macro]))] `(def ~n ~(var-get v))))]
        (if (symbol? s) (f s) (-/cons 'do (map f s)))
    )
)

(refer! clojure.core [-> and cond cons defmacro identical? list or])

(defn throw! [& s] (throw (Error. (apply str s))))

(defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))

(defn #_"int" Integer'parseInt [#_"String" s] (Integer/parseInt s))

(defn #_"StringBuilder" StringBuilder'new [] (StringBuilder.))

(defn #_"StringBuilder" StringBuilder''append   [^StringBuilder this, #_"char" ch] (.append this, ch))
(defn #_"String"        StringBuilder''toString [^StringBuilder this]              (.toString this))

(def System'in  *in*)
(def System'out *out*)

(defn #_"void" Flushable''flush [^Flushable this] (.flush this))

(defn #_"void" PushbackReader''unread [^PushbackReader this, #_"int" x] (.unread this, x))

(defn #_"int" Reader''read [^Reader this] (.read this))

(defn #_"Pattern" Pattern'compile  [#_"String" s]                (Pattern/compile s))
(defn #_"Matcher" Pattern''matcher [^Pattern this, #_"String" s] (.matcher this, s))

(defn #_"boolean" Matcher''matches [^Matcher this] (.matches this))

(defn #_"var" Namespace''findInternedVar [^Namespace this, #_"Symbol" name] (.findInternedVar this, name))

(defn #_"any" Var''-get [^Var this] (.get this))

(def -=            =)
(def -aget         aget)
(def -alength      alength)
(def -apply        apply)

(defn -array? [x] (and (some? x) (.isArray (class x))))

(def -aset         aset)
(def -boolean?     boolean?)
(def -char         char)
(def -char?        char?)
(def -conj         conj)
(def -first        first)
(def -fn?          fn?)
(def -int          int)
(def -name         name)
(def -namespace    namespace)
(def -neg?         neg?)
(def -next         next)
(def -number?      number?)
(def -object-array object-array)
(def -seq          seq)
(def -seq?         seq?)
(def -seqable?     seqable?)
(def -str          str)
(def -string?      string?)
(def -symbol       symbol)
(def -symbol?      symbol?)
(def -the-ns       the-ns)
(def -var?         var?)

(ns beagle.core
    (:refer-clojure :only [])
    (:require [beagle.bore :as -])
)

(-/import!)

(-/refer! beagle.bore [-> -= Appendable''append Flushable''flush Integer'parseInt Matcher''matches Namespace''findInternedVar Pattern''matcher Pattern'compile PushbackReader''unread Reader''read StringBuilder''append StringBuilder''toString StringBuilder'new System'in System'out Var''-get -aget -alength and -apply -array? -aset -boolean? -char -char? cond -conj cons -first -fn? identical? -int list -name -namespace -neg? -next -number? -object-array or -seq -seq? -seqable? -str -string? -symbol -symbol? -the-ns throw! -var?])

(-/defmacro about   [& s]   (-/cons 'do s))
(-/defmacro declare [x]     (-/list 'def x nil))
(-/defmacro when    [? & s] (-/list 'if ? (-/cons 'do s) nil))

(-/defmacro fn   [& s] (-/cons 'fn* s))
(-/defmacro let  [& s] (-/cons 'let* s))
(-/defmacro loop [& s] (-/cons 'loop* s))

(-/defmacro defn     [f & s] (-/list 'def f (-/cons 'fn s)))
(-/defmacro lazy-seq [& s]   (-/cons 'fn (-/cons [] s)))

(def identical? -/identical?)

(defn identity [x] x)

(defn nil?   [x] (identical? x nil))
(defn true?  [x] (identical? x true))
(defn false? [x] (identical? x false))
(defn not    [x] (if x false true))
(defn some?  [x] (not (nil? x)))

(about #_"array"
    (defn anew [n] (-/-object-array n))

    (defn aget    [a i]   (-/-aget a i))
    (defn alength [a]     (-/-alength a))
    (defn aset!   [a i x] (-/-aset a i x) a)

    (defn volatile-acas! [a i x y] (when (identical? (aget a i) x) (aset! a i y)))
    (defn volatile-aget  [a i]     (aget a i))
    (defn volatile-aset! [a i x]   (aset! a i x))
)

(about #_"seq"
    (declare cons?)
    (declare Cons''seq)
    (declare closure?)
    (declare Closure''seq)

    (defn seq [s]
        (cond
            (nil? s)         nil
            (cons? s)        (Cons''seq s)
            (closure? s)     (Closure''seq s)
            (-/-seqable? s)  (-/-seq s)
            'else            (-/throw! "seq not supported on " s)
        )
    )

    (declare Cons''first)

    (defn first [s]
        (let [s (seq s)]
            (cond
                (nil? s)    nil
                (cons? s)   (Cons''first s)
                (-/-seq? s) (-/-first s)
                'else       (-/throw! "first not supported on " s)
            )
        )
    )

    (declare Cons''next)

    (defn next [s]
        (let [s (seq s)]
            (cond
                (nil? s)    nil
                (cons? s)   (Cons''next s)
                (-/-seq? s) (-/-next s)
                'else       (-/throw! "next not supported on " s)
            )
        )
    )

    (defn second [s] (first (next s)))
    (defn third  [s] (first (next (next s))))
    (defn fourth [s] (first (next (next (next s)))))

    (defn reduce [f r s] (let [s (seq s)] (if (some? s) (#_recur reduce f (f r (first s)) (next s)) r)))

    (defn reduce-kv [f r kvs] (let [kvs (seq kvs)] (if (some? kvs) (#_recur reduce-kv f (f r (first kvs) (second kvs)) (next (next kvs))) r)))
)

(about #_"unicode"
    (def Unicode'newline     10)
    (def Unicode'escape      27)
    (def Unicode'space       32)
    (def Unicode'quotation   34)
    (def Unicode'hash        35)
    (def Unicode'apostrophe  39)
    (def Unicode'lparen      40)
    (def Unicode'rparen      41)
    (def Unicode'comma       44)
    (def Unicode'minus       45)
    (def Unicode'slash       47)
    (def Unicode'0           48)
    (def Unicode'1           49)
    (def Unicode'2           50)
    (def Unicode'3           51)
    (def Unicode'4           52)
    (def Unicode'5           53)
    (def Unicode'6           54)
    (def Unicode'7           55)
    (def Unicode'8           56)
    (def Unicode'9           57)
    (def Unicode'lbracket    91)
    (def Unicode'backslash   92)
    (def Unicode'rbracket    93)
    (def Unicode'underscore  95)
    (def Unicode'grave       96)
    (def Unicode'n          110)
)

(about #_"beagle.Atom"

(about #_"Atom"
    (defn #_"Atom" Atom'new [#_"any" init]
        (-> (anew 2) (aset! 0 "Atom'meta") (volatile-aset! 1 init))
    )

    (declare =)

    (defn atom? [x] (and (-/-array? x) (= (alength x) 2) (= (aget x 0) "Atom'meta")))

    (defn #_"any" Atom''deref [#_"Atom" this]
        (volatile-aget this 1)
    )

    (declare apply)

    (defn #_"any" Atom''swap [#_"Atom" this, #_"fn" f, #_"seq" s]
        (loop []
            (let [#_"any" o (volatile-aget this 1) #_"any" o' (apply f o s)]
                (if (volatile-acas! this 1 o o') o' (recur))
            )
        )
    )

    (defn #_"any" Atom''reset [#_"Atom" this, #_"any" o']
        (volatile-aset! this 1 o')
        o'
    )
)

(defn atom [x] (Atom'new x))

(defn deref [a]
    (cond
        (atom? a) (Atom''deref a)
        'else     (-/throw! "deref not supported on " a)
    )
)

(defn swap! [a f & s]
    (cond
        (atom? a) (Atom''swap a, f, s)
        'else     (-/throw! "swap! not supported on " a)
    )
)

(defn reset! [a x]
    (cond
        (atom? a) (Atom''reset a, x)
        'else     (-/throw! "reset! not supported on " a)
    )
)
)

(about #_"beagle.Cons"

(about #_"Cons"
    (defn #_"Cons" Cons'new [#_"any" car, #_"seq" cdr]
        (-> (anew 3) (aset! 0 "Cons'meta") (aset! 1 car) (aset! 2 cdr))
    )

    (defn cons? [x] (and (-/-array? x) (= (alength x) 3) (= (aget x 0) "Cons'meta")))

    (defn #_"any" Cons''car [#_"Cons" this] (when (cons? this) (aget this 1)))
    (defn #_"seq" Cons''cdr [#_"Cons" this] (when (cons? this) (aget this 2)))

    (defn #_"seq" Cons''seq [#_"Cons" this]
        this
    )

    (defn #_"any" Cons''first [#_"Cons" this]      (Cons''car this))
    (defn #_"seq" Cons''next  [#_"Cons" this] (seq (Cons''cdr this)))

    (defn #_"boolean" Cons''equals [#_"Cons" this, #_"any" that]
        (or (identical? this that)
            (and (or (cons? that) (-/-seqable? that))
                (loop [#_"seq" s (seq this) #_"seq" z (seq that)]
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
        (nil? s)        nil
        (nil? (next s)) (seq (first s))
        'else           (cons (first s) (spread (next s)))
    )
)

(defn reverse [s] (reduce conj nil s))

(defn list [& s] s)

(defn reverse! [s] (reduce -/-conj (-/list) s))

(defn some [f s]
    (let [s (seq s)]
        (when (some? s)
            (or (f (first s)) (#_recur some f (next s)))
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
)

(about #_"beagle.ConsMap"

(about #_"ConsMap"
    (defn #_"ConsMap" ConsMap'new [#_"key" caar, #_"value" cadar, #_"seq" cdr]
        (cons (cons caar (cons cadar nil)) cdr)
    )

    (defn #_"Cons" ConsMap''find [#_"ConsMap" this, #_"key" key]
        (some (fn [#_"Cons?" e] (when (and (cons? e) (= (first e) key)) e)) this)
    )

    (defn #_"boolean" ConsMap''contains? [#_"ConsMap" this, #_"key" key]
        (some? (ConsMap''find this, key))
    )

    (defn #_"value" ConsMap''get [#_"ConsMap" this, #_"key" key]
        (second (ConsMap''find this, key))
    )

    (defn #_"ConsMap" ConsMap''assoc [#_"ConsMap" this, #_"key" key, #_"value" val]
        (if (let [#_"Cons?" e (first this)] (and (cons? e) (#_= identical? (first e) key) (#_= identical? (second e) val)))
            this
            (ConsMap'new key, val, this)
        )
    )

    (defn #_"seq" Cons''keys [#_"Cons" this]
        (loop [#_"seq" z nil #_"seq" s (seq this)]
            (if (some? s)
                (recur (cons (first s) z) (next (next s)))
                (reverse z)
            )
        )
    )

    (defn #_"seq" Cons''vals [#_"Cons" this]
        (loop [#_"seq" z nil #_"seq" s (seq this)]
            (if (some? s)
                (recur (cons (second s) z) (next (next s)))
                (reverse z)
            )
        )
    )
)

(defn assoc [m k v]
    (cond
        (nil? m)  (ConsMap'new k, v, nil)
        (cons? m) (ConsMap''assoc m, k, v)
        'else     (-/throw! "assoc not supported on " m)
    )
)

(defn cons-map [& kvs] (reduce-kv assoc nil kvs))

(defn contains? [m k]
    (cond
        (nil? m)  false
        (cons? m) (ConsMap''contains? m, k)
        'else     (-/throw! "contains? not supported on " m)
    )
)

(defn get [m k]
    (cond
        (nil? m)  nil
        (cons? m) (ConsMap''get m, k)
        'else     (-/throw! "get not supported on " m)
    )
)

(defn update [m k f & s] (assoc m k (apply f (get m k) s)))
)

(about #_"beagle.Symbol"

(about #_"Symbol"
    (defn #_"Symbol" Symbol'new [#_"String" ns, #_"String" name]
        (-> (anew 3) (aset! 0 "Symbol'meta") (aset! 1 ns) (aset! 2 name))
    )

    (defn symbol? [x] (and (-/-array? x) (= (alength x) 3) (= (aget x 0) "Symbol'meta")))

    (defn #_"String" Symbol''ns   [#_"Symbol" this] (when (symbol? this) (aget this 1)))
    (defn #_"String" Symbol''name [#_"Symbol" this] (when (symbol? this) (aget this 2)))

    (defn #_"Symbol" Symbol'create [#_"String" name]
        (if (and (= (-/-int (first name)) Unicode'minus) (= (-/-int (second name)) Unicode'slash))
            (Symbol'new "-", (apply -/-str (next (next name))))
            (Symbol'new nil, name)
        )
    )

    (defn #_"boolean" Symbol''equals [#_"Symbol" this, #_"any" that]
        (or (identical? this that)
            (and (or (symbol? that) (-/-symbol? that))
                (= (Symbol''ns this) (if (-/-symbol? that) (-/-namespace that) (Symbol''ns that)))
                (= (Symbol''name this) (if (-/-symbol? that) (-/-name that) (Symbol''name that)))
            )
        )
    )
)

(defn symbol [name] (if (or (symbol? name) (-/-symbol? name)) name (Symbol'create name)))

(defn symbol! [s] (symbol (if (-/-symbol? s) (-/-str s) s)))
)

(about #_"beagle.Closure"

(about #_"Closure"
    (defn #_"Closure" Closure'new [#_"FnExpr" fun, #_"map" env]
        (-> (anew 3) (aset! 0 "Closure'meta") (aset! 1 fun) (aset! 2 env))
    )

    (defn closure? [x] (and (-/-array? x) (= (alength x) 3) (= (aget x 0) "Closure'meta")))

    (defn #_"FnExpr" Closure''fun [#_"Closure" this] (when (closure? this) (aget this 1)))
    (defn #_"map"    Closure''env [#_"Closure" this] (when (closure? this) (aget this 2)))

    (declare Code''emit)
    (declare Machine'compute)

    (defn #_"any" Closure''applyTo [#_"Closure" this, #_"seq" args]
        (let [
            #_"FnExpr" fun (Closure''fun this) #_"map" env (Closure''env this)
            env
                (let [#_"Symbol" x (get fun 'self)]
                    (if (some? x) (assoc env x this) env)
                )
            env
                (loop [env env #_"seq" pars (seq (get fun 'pars)) args (seq args)]
                    (if (some? pars)
                        (recur (assoc env (first pars) (first args)) (next pars) (next args))
                        (let [#_"Symbol" x (get fun 'etal)]
                            (if (some? x) (assoc env x args) env)
                        )
                    )
                )
            #_"seq" code (-> nil (Code''emit (get fun 'body)) reverse)
        ]
            (Machine'compute code, env)
        )
    )

    (defn #_"seq" Closure''seq [#_"Closure" this]
        (cons (Closure''applyTo this, nil) nil)
    )
)

(defn apply [f & s]
    (let [s (spread s)]
        (cond
            (closure? f) (Closure''applyTo f, s)
            (atom? f)    (apply (deref f) s)
            (-/-fn? f)   (-/-apply f (reverse! (reverse s)))
            'else        (-/throw! "apply not supported on " f)
        )
    )
)
)

(about #_"beagle.Var"

(about #_"Var"
    (defn #_"Var" Var'new []
        (atom nil)
    )

    (defn #_"any" Var''get [#_"Var" this]
        (if (-/-var? this) (-/Var''-get this) (deref this))
    )

    (defn #_"void" Var''bindRoot [#_"Var" this, #_"any" root]
        (reset! this root)
        nil
    )
)
)

(about #_"equivalence"

(defn = [x y]
    (cond
        (identical? x y) true
        (or (nil? x) (nil? y) (true? x) (true? y) (false? x) (false? y)) false
        (symbol? x)      (Symbol''equals x, y)
        (symbol? y)      (Symbol''equals y, x)
        (cons? x)        (Cons''equals x, y)
        (cons? y)        (Cons''equals y, x)
        (or (-/-boolean? x) (-/-char? x) (-/-number? x) (-/-string? x) (-/-symbol? x)) (-/-= x y)
        'else            (-/throw! "= not supported on " x ", not even on " y)
    )
)
)

(about #_"append"
    (defn #_"char|String" escape-str [#_"char" c]
        (cond
            (= (-/-int c) Unicode'newline)   "\\n"
            (= (-/-int c) Unicode'quotation) "\\\""
            (= (-/-int c) Unicode'backslash) "\\\\"
            'else                           c
        )
    )

    (defn #_"Appendable" append-str [#_"Appendable" a, #_"String" x]
        (let [
            a (-/Appendable''append a, "\"")
            a (reduce (fn [%1 %2] (-/Appendable''append %1, (escape-str %2))) a x)
            a (-/Appendable''append a, "\"")
        ]
            a
        )
    )

    (defn #_"Appendable" append-sym [#_"Appendable" a, #_"Symbol" x]
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
    )

    (defn #_"Appendable" append* [#_"Appendable" a, #_"String" b, #_"fn" f'append, #_"String" c, #_"String" d, #_"Seqable" q]
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
    )

    (declare append)

    (defn #_"Appendable" append-seq [#_"Appendable" a, #_"seq" x] (append* a "(" append " " ")" x))

    (defn #_"Appendable" append [#_"Appendable" a, #_"any" x]
        (cond
            (nil? x)       (-/Appendable''append a, "nil")
            (true? x)      (-/Appendable''append a, "true")
            (false? x)     (-/Appendable''append a, "false")
            (-/-number? x) (-/Appendable''append a, (-/-str x))
            (-/-string? x) (append-str a x)
            (symbol? x)    (append-sym a x)
            (cons? x)      (append-seq a x)
            (atom? x)      (-/Appendable''append a, "atom")
            (closure? x)   (-/Appendable''append a, "closure")
            'else          (-/Appendable''append a, "object")
        )
    )

    (defn #_"Appendable" append! [#_"Appendable" a, #_"any" x]
        (if (or (-/-symbol? x) (-/-string? x) (-/-char? x)) (-/Appendable''append a, x) (append a x))
    )

    (defn #_"String" str [& s]
        (loop [#_"StringBuilder" sb (-/StringBuilder'new) s s]
            (if (some? s)
                (let [x (first s)]
                    (recur (if (some? x) (append! sb x) sb) (next s))
                )
                (-/StringBuilder''toString sb)
            )
        )
    )

    (defn space   [] (-/Appendable''append -/System'out (-/-char Unicode'space))   nil)
    (defn newline [] (-/Appendable''append -/System'out (-/-char Unicode'newline)) nil)
    (defn flush   [] (-/Flushable''flush   -/System'out)                           nil)

    (defn pr [& s]
        (when (some? s)
            (loop [x (first s) s (next s)]
                (append -/System'out x)
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
                (append! -/System'out x)
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

(about #_"beagle.Compiler"

(about #_"Code"
    (defn #_"seq" Code''apply    [#_"seq" code]                             (cons (list 'apply) code))
    (defn #_"seq" Code''cons     [#_"seq" code]                             (cons (list 'cons) code))
    (defn #_"seq" Code''closure  [#_"seq" code, #_"FnExpr" fun]             (cons (list 'closure fun) code))
    (defn #_"seq" Code''get      [#_"seq" code, #_"Symbol" name]            (cons (list 'get name) code))
    (defn #_"seq" Code''if       [#_"seq" code, #_"seq" then, #_"seq" else] (cons (list 'if then else) code))
    (defn #_"seq" Code''pop      [#_"seq" code]                             (cons (list 'pop) code))
    (defn #_"seq" Code''push     [#_"seq" code, #_"any" value]              (cons (list 'push value) code))
    (defn #_"seq" Code''var-get  [#_"seq" code, #_"Var" var]                (cons (list 'var-get var) code))
    (defn #_"seq" Code''var-set! [#_"seq" code, #_"Var" var]                (cons (list 'var-set! var) code))
)

(about #_"LiteralExpr"
    (defn #_"LiteralExpr" LiteralExpr'new [#_"any" value]
        (cons-map
            #_"meta" 'meta "LiteralExpr'meta"
            #_"any" 'value value
        )
    )

    (def #_"LiteralExpr" LiteralExpr'NIL   (LiteralExpr'new nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (LiteralExpr'new true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (LiteralExpr'new false))

    (defn #_"Expr" LiteralExpr'parse [#_"seq" form, #_"seq" scope]
        (cond
            (nil? (next form))         (-/throw! "too few arguments to quote")
            (some? (next (next form))) (-/throw! "too many arguments to quote")
        )
        (let [#_"any" x (second form)]
            (cond
                (nil? x)    LiteralExpr'NIL
                (true? x)   LiteralExpr'TRUE
                (false? x)  LiteralExpr'FALSE
                'else      (LiteralExpr'new x)
            )
        )
    )

    (defn #_"seq" LiteralExpr''emit [#_"LiteralExpr" this, #_"seq" code]
        (Code''push code, (get this 'value))
    )
)

(about #_"VarExpr"
    (defn #_"VarExpr" VarExpr'new [#_"Var" var]
        (cons-map
            #_"meta" 'meta "VarExpr'meta"
            #_"Var" 'var var
        )
    )

    (defn #_"seq" VarExpr''emit [#_"VarExpr" this, #_"seq" code]
        (Code''var-get code, (get this 'var))
    )
)

(about #_"BodyExpr"
    (defn #_"BodyExpr" BodyExpr'new [#_"Expr*" exprs]
        (cons-map
            #_"meta" 'meta "BodyExpr'meta"
            #_"Expr*" 'exprs exprs
        )
    )

    (declare Compiler'analyze)

    (defn #_"Expr" BodyExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"Expr*" z
                (loop [z nil #_"seq" s (next form)]
                    (if (some? s)
                        (recur (cons (Compiler'analyze (first s), scope) z) (next s))
                        (reverse z)
                    )
                )
        ]
            (BodyExpr'new (or (#_seq identity z) (list LiteralExpr'NIL)))
        )
    )

    (defn #_"seq" BodyExpr''emit [#_"BodyExpr" this, #_"seq" code]
        (loop [code code #_"seq" s (seq (get this 'exprs))]
            (let [
                code (Code''emit code, (first s))
            ]
                (if (some? (next s))
                    (recur (Code''pop code) (next s))
                    code
                )
            )
        )
    )
)

(about #_"IfExpr"
    (defn #_"IfExpr" IfExpr'new [#_"Expr" test, #_"Expr" then, #_"Expr" else]
        (cons-map
            #_"meta" 'meta "IfExpr'meta"
            #_"Expr" 'test test
            #_"Expr" 'then then
            #_"Expr" 'else else
        )
    )

    (defn #_"Expr" IfExpr'parse [#_"seq" form, #_"seq" scope]
        (cond
            (nil? (next (next (next form))))         (-/throw! "too few arguments to if")
            (some? (next (next (next (next form))))) (-/throw! "too many arguments to if")
        )
        (let [
            #_"Expr" test (Compiler'analyze (second form), scope)
            #_"Expr" then (Compiler'analyze (third form), scope)
            #_"Expr" else (Compiler'analyze (fourth form), scope)
        ]
            (IfExpr'new test, then, else)
        )
    )

    (defn #_"seq" IfExpr''emit [#_"IfExpr" this, #_"seq" code]
        (-> code
            (Code''emit (get this 'test))
            (Code''if
                (-> nil (Code''emit (get this 'then)) reverse),
                (-> nil (Code''emit (get this 'else)) reverse)
            )
        )
    )
)

(about #_"InvokeExpr"
    (defn #_"InvokeExpr" InvokeExpr'new [#_"Expr" fexpr, #_"Expr*" rargs]
        (cons-map
            #_"meta" 'meta "InvokeExpr'meta"
            #_"Expr" 'fexpr fexpr
            #_"Expr*" 'rargs rargs
        )
    )

    (defn #_"Expr" InvokeExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"Expr" fexpr (Compiler'analyze (first form), scope)
            #_"Expr*" rargs (reduce (fn [%1 %2] (conj %1 (Compiler'analyze %2, scope))) nil (next form))
        ]
            (InvokeExpr'new fexpr, rargs)
        )
    )

    (defn #_"seq" InvokeExpr'emitArgs [#_"seq" code, #_"Expr*" rargs]
        (loop [code (Code''push code, nil) #_"seq" s (seq rargs)]
            (if (some? s)
                (let [
                    code (Code''emit code, (first s))
                    code (Code''cons code)
                ]
                    (recur code (next s))
                )
                code
            )
        )
    )

    (defn #_"seq" InvokeExpr''emit [#_"InvokeExpr" this, #_"seq" code]
        (-> code
            (Code''emit (get this 'fexpr))
            (InvokeExpr'emitArgs (get this 'rargs))
            (Code''apply)
        )
    )
)

(about #_"BindingExpr"
    (defn #_"BindingExpr" BindingExpr'new [#_"Symbol" sym]
        (cons-map
            #_"meta" 'meta "BindingExpr'meta"
            #_"Symbol" 'sym sym
        )
    )

    (defn #_"seq" BindingExpr''emit [#_"BindingExpr" this, #_"seq" code]
        (Code''get code, (get this 'sym))
    )
)

(about #_"FnExpr"
    (defn #_"FnExpr" FnExpr'new [#_"Symbol" self]
        (cons-map
            #_"meta" 'meta "FnExpr'meta"
            #_"Symbol" 'self self
            #_"Symbol*" 'pars nil
            #_"Symbol" 'etal nil
            #_"Expr" 'body nil
        )
    )

    (defn #_"FnExpr" FnExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"symbol?" name (second form) ? (or (symbol? name) (-/-symbol? name)) name (when ? name) form (if ? (next (next form)) (next form))
            #_"FnExpr" fun
                (loop [fun (FnExpr'new name) #_"boolean" variadic? false #_"seq" s (seq (first form))]
                    (if (some? s)
                        (let [#_"symbol?" sym (first s)]
                            (if (or (symbol? sym) (-/-symbol? sym))
                                (let [sym (symbol! sym)]
                                    (if (nil? (Symbol''ns sym))
                                        (cond
                                            (= sym '&)
                                                (if (not variadic?)
                                                    (recur fun true (next s))
                                                    (-/throw! "overkill variadic parameter list")
                                                )
                                            (some? (get fun 'etal))
                                                (-/throw! "excess variadic parameter " sym)
                                            'else
                                                (let [fun (if (not variadic?) (update fun 'pars conj sym) (assoc fun 'etal sym))]
                                                    (recur fun variadic? (next s))
                                                )
                                        )
                                        (-/throw! "can't use qualified name as parameter " sym)
                                    )
                                )
                                (-/throw! "function parameters must be symbols")
                            )
                        )
                        (if (or (not variadic?) (some? (get fun 'etal)))
                            (update fun 'pars reverse)
                            (-/throw! "missing variadic parameter")
                        )
                    )
                )
            scope
                (let [#_"Symbol" x (get fun 'self)]
                    (if (some? x) (cons x scope) scope)
                )
            scope
                (loop [scope scope #_"seq" pars (seq (get fun 'pars))]
                    (if (some? pars)
                        (recur (cons (first pars) scope) (next pars))
                        (let [#_"Symbol" x (get fun 'etal)]
                            (if (some? x) (cons x scope) scope)
                        )
                    )
                )
        ]
            (assoc fun 'body (BodyExpr'parse (cons 'do (next form)), scope))
        )
    )

    (defn #_"seq" FnExpr''emit [#_"FnExpr" this, #_"seq" code]
        (Code''closure code, this)
    )
)

(about #_"DefExpr"
    (defn #_"DefExpr" DefExpr'new [#_"Var" var, #_"Expr" init]
        (cons-map
            #_"meta" 'meta "DefExpr'meta"
            #_"Var" 'var var
            #_"Expr" 'init init
        )
    )

    (def #_"map'" Beagle'ns (atom nil))

    (defn #_"Var" DefExpr'lookupVar [#_"Symbol" sym]
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
    )

    (defn #_"Expr" DefExpr'parse [#_"seq" form, #_"seq" scope]
        (cond
            (nil? (next (next form)))         (-/throw! "too few arguments to def")
            (some? (next (next (next form)))) (-/throw! "too many arguments to def")
        )
        (let [#_"symbol?" s (second form)]
            (if (or (symbol? s) (-/-symbol? s))
                (DefExpr'new (DefExpr'lookupVar s), (Compiler'analyze (third form), scope))
                (-/throw! "first argument to def must be a symbol")
            )
        )
    )

    (defn #_"seq" DefExpr''emit [#_"DefExpr" this, #_"seq" code]
        (-> code
            (Code''emit (get this 'init))
            (Code''var-set! (get this 'var))
        )
    )
)

(about #_"Code"
    (defn #_"seq" Code''emit [#_"seq" code, #_"Expr" expr]
        (let [#_"meta" m (get expr 'meta)]
            (cond
                (= m "LiteralExpr'meta") (LiteralExpr''emit expr, code)
                (= m "VarExpr'meta")     (VarExpr''emit expr, code)
                (= m "BodyExpr'meta")    (BodyExpr''emit expr, code)
                (= m "IfExpr'meta")      (IfExpr''emit expr, code)
                (= m "InvokeExpr'meta")  (InvokeExpr''emit expr, code)
                (= m "BindingExpr'meta") (BindingExpr''emit expr, code)
                (= m "FnExpr'meta")      (FnExpr''emit expr, code)
                (= m "DefExpr'meta")     (DefExpr''emit expr, code)
                'else                    (-/throw! "Code''emit not supported on " expr)
            )
        )
    )
)

(about #_"Compiler"
    (def #_"map" Compiler'specials
        (cons-map
            '&          nil
            'def        DefExpr'parse
            'do         BodyExpr'parse
            'ζ          FnExpr'parse
            'if         IfExpr'parse
            'quote      LiteralExpr'parse
        )
    )

    (def #_"map" Compiler'macros
        (cons-map
            'about      (fn [& s]   (cons 'do s))
            'declare    (fn [x]     (list 'def x nil))
            'when       (fn [? & s] (list 'if ? (cons 'do s) nil))
            'cond       (fn [& s]   (when s (list 'if (first s) (second s) (cons 'cond (next (next s))))))
            'and        (fn [& s]   (if s (let [x (first s) s (next s)] (if s (list 'let (list '&and x) (list 'if '&and (cons 'and s) '&and)) x)) true))
            'or         (fn [& s]   (when s (let [x (first s) s (next s)] (if s (list 'let (list '&or x) (list 'if '&or '&or (cons 'or s))) x))))
            '->         (fn [x & s] (loop [x x s s] (if s (recur (let [f (first s)] (if (or (cons? f) (-/-seq? f)) (cons (first f) (cons x (next f))) (list f x))) (next s)) x)))
            'fn         (fn [& s]   (cons 'ζ s))
            'let        (fn [a & s] (if (seq a) (list (list 'fn (list (first a)) (cons 'let (cons (next (next a)) s))) (second a)) (cons 'do s)))
            'loop       (fn [a & s] (cons (cons 'fn (cons 'recur (cons (Cons''keys a) s))) (Cons''vals a)))
            'defn       (fn [f & s] (list 'def f (cons 'fn s)))
            'lazy-seq   (fn [& s]   (cons 'fn (cons [] s)))
        )
    )

    (defn #_"edn" Compiler'macroexpand1 [#_"edn" form]
        (if (or (cons? form) (-/-seq? form))
            (let [#_"fn" f'macro (get Compiler'macros (first form))]
                (if (some? f'macro) (apply f'macro (next form)) form)
            )
            form
        )
    )

    (defn #_"edn" Compiler'macroexpand [#_"edn" form]
        (let [#_"edn" me (Compiler'macroexpand1 form)]
            (if (#_= identical? me form) form (#_recur Compiler'macroexpand me))
        )
    )

    (defn #_"Expr" Compiler'analyzeSymbol [#_"Symbol" sym, #_"seq" scope]
        (let [sym (symbol! sym)]
            (or
                (when (and (nil? (Symbol''ns sym)) (some (fn [%] (= % sym)) scope))
                    (BindingExpr'new sym)
                )
                (let [#_"any" o
                        (if (some? (Symbol''ns sym))
                            (-/Namespace''findInternedVar (-/-the-ns (-/-symbol "beagle.core")), (-/-symbol (Symbol''name sym)))
                            (get (deref Beagle'ns) sym)
                        )]
                    (if (some? o)
                        (VarExpr'new o)
                        (-/throw! "unable to resolve symbol " sym)
                    )
                )
            )
        )
    )

    (defn #_"Expr" Compiler'analyzeSeq [#_"seq" form, #_"seq" scope]
        (let [#_"edn" me (Compiler'macroexpand1 form)]
            (if (#_= identical? me form)
                (let [#_"any" op (first form)]
                    (if (some? op)
                        (let [#_"fn" f'parse (or (get Compiler'specials op) InvokeExpr'parse)]
                            (f'parse form scope)
                        )
                        (-/throw! "can't call nil in form " form)
                    )
                )
                (Compiler'analyze me, scope)
            )
        )
    )

    (defn #_"Expr" Compiler'analyze [#_"edn" form, #_"seq" scope]
        (cond
            (nil? form)                                           LiteralExpr'NIL
            (true? form)                                          LiteralExpr'TRUE
            (false? form)                                         LiteralExpr'FALSE
            (or (symbol? form) (-/-symbol? form))                (Compiler'analyzeSymbol form, scope)
            (or (cons? form) (and (-/-seq? form) (-/-seq form))) (Compiler'analyzeSeq form, scope)
            'else                                                (LiteralExpr'new form)
        )
    )

    (defn #_"edn" Compiler'eval [#_"edn" form]
        (let [form (Compiler'macroexpand form)]
            (apply (Closure'new (Compiler'analyze (list (symbol! 'fn) [] form), nil), nil) nil)
        )
    )
)

(defn eval [form] (Compiler'eval form))
)

(about #_"machine"
    (defn #_"any" Machine'compute [#_"seq" code, #_"map" env]
        (loop [#_"stack" s nil code (seq code)]
            (if (some? code)
                (let [xyz (first code) x (first xyz) y (second xyz) z (third xyz)]
                    (cond
                        (= x 'apply)    (let [b (first s) a (second s) s (next (next s))] (recur (cons (apply a b) s)                       (next code)))
                        (= x 'cons)     (let [b (first s) a (second s) s (next (next s))] (recur (cons (cons b a) s)                        (next code)))
                        (= x 'get)                                                        (recur (cons (get env y) s)                       (next code))
                        (= x 'if)       (let [a (first s)              s (next s)]        (recur (cons (Machine'compute (if a y z), env) s) (next code)))
                        (= x 'closure)                                                    (recur (cons (Closure'new y, env) s)              (next code))
                        (= x 'pop)                                                        (recur (next s)                                   (next code))
                        (= x 'push)                                                       (recur (cons y s)                                 (next code))
                        (= x 'var-get)                                                    (recur (cons (Var''get y) s)                      (next code))
                        (= x 'var-set!) (let [a (first s)              s (next s)]        (recur (cons (Var''bindRoot y, a) s)              (next code)))
                    )
                )
                (first s)
            )
        )
    )
)

(about #_"beagle.LispReader"

(about #_"LispReader"
    (declare LispReader'macros)

    (defn #_"boolean" LispReader'isMacro [#_"unicode" c]
        (some? (get LispReader'macros c))
    )

    (defn #_"boolean" LispReader'isTerminatingMacro [#_"unicode" c]
        (and (LispReader'isMacro c) (not (= c Unicode'hash)) (not (= c Unicode'apostrophe)))
    )

    (defn #_"boolean" LispReader'isDigit [#_"unicode" c]
        (or (= c Unicode'0) (= c Unicode'1) (= c Unicode'2) (= c Unicode'3) (= c Unicode'4) (= c Unicode'5) (= c Unicode'6) (= c Unicode'7) (= c Unicode'8) (= c Unicode'9))
    )

    (def #_"unicode" LispReader'naught 31)

    (defn #_"boolean" LispReader'isWhitespace [#_"unicode" c]
        (or (= c Unicode'space) (= c Unicode'comma) (= c Unicode'newline) (= c LispReader'naught))
    )

    (defn #_"Unicode" LispReader'read1 [#_"Reader" r]
        (let [#_"unicode" c (-/Reader''read r)]
            (when (not (-/-neg? c))
                c
            )
        )
    )

    (defn #_"void" LispReader'unread [#_"PushbackReader" r, #_"Unicode" c]
        (when (some? c)
            (-/PushbackReader''unread r, c)
        )
        nil
    )

    (def #_"Pattern" LispReader'rxInteger (-/Pattern'compile "0|[1-9][0-9]*"))

    (defn #_"number" LispReader'matchNumber [#_"String" s]
        (let [#_"Matcher" m (-/Pattern''matcher LispReader'rxInteger, s)]
            (when (-/Matcher''matches m)
                (-/Integer'parseInt s)
            )
        )
    )

    (defn #_"number" LispReader'readNumber [#_"PushbackReader" r, #_"unicode" c]
        (let [#_"String" s
                (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, (-/-char c))]
                    (loop []
                        (let [c (LispReader'read1 r)]
                            (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isMacro c))
                                (do
                                    (LispReader'unread r, c)
                                    (-/StringBuilder''toString sb)
                                )
                                (do
                                    (-/StringBuilder''append sb, (-/-char c))
                                    (recur)
                                )
                            )
                        )
                    )
                )]
            (or (LispReader'matchNumber s) (-/throw! "invalid number " s))
        )
    )

    (defn #_"String" LispReader'readToken [#_"PushbackReader" r, #_"unicode" c]
        (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, (-/-char c))]
            (loop []
                (let [c (LispReader'read1 r)]
                    (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isTerminatingMacro c))
                        (do
                            (LispReader'unread r, c)
                            (-/StringBuilder''toString sb)
                        )
                        (do
                            (-/StringBuilder''append sb, (-/-char c))
                            (recur)
                        )
                    )
                )
            )
        )
    )

    #_"\n !\"#%&'()*,-./0123456789=>?ABCDEFHILMNOPRSTUVWZ[\\]_abcdefghijklmnopqrstuvwxyz|ζ"

    (def #_"Pattern" LispReader'rxSymbol (-/Pattern'compile "(-/)?[-a-zA-Z_*?!=>&%ζ][-a-zA-Z_*?!=>&%0-9'#]*"))

    (defn #_"symbol" LispReader'matchSymbol [#_"String" s]
        (let [#_"Matcher" m (-/Pattern''matcher LispReader'rxSymbol, s)]
            (when (-/Matcher''matches m)
                (symbol s)
            )
        )
    )

    (defn #_"symbol" LispReader'interpretToken [#_"String" s]
        (cond (= s "nil") nil (= s "true") true (= s "false") false 'else
            (or (LispReader'matchSymbol s) (-/throw! "invalid token " s))
        )
    )

    (defn #_"any" LispReader'read [#_"PushbackReader" r, #_"seq" scope, #_"Unicode" delim, #_"any" delim!]
        (loop []
            (let [#_"Unicode" c (loop [c (LispReader'read1 r)] (if (and (some? c) (LispReader'isWhitespace c)) (recur (LispReader'read1 r)) c))]
                (cond
                    (nil? c)
                        (-/throw! "EOF while reading")
                    (and (some? delim) (= delim c))
                        delim!
                    (LispReader'isDigit c)
                        (LispReader'readNumber r, c)
                    'else
                        (let [#_"fn" f'macro (get LispReader'macros c)]
                            (if (some? f'macro)
                                (let [#_"any" o (f'macro r scope c)]
                                    (if (identical? o r) (recur) o)
                                )
                                (LispReader'interpretToken (LispReader'readToken r, c))
                            )
                        )
                )
            )
        )
    )

    (def #_"any" LispReader'READ_FINISHED (anew 0))

    (defn #_"seq" LispReader'readDelimitedForms [#_"PushbackReader" r, #_"seq" scope, #_"unicode" delim]
        (loop [#_"seq" z nil]
            (let [#_"any" form (LispReader'read r, scope, delim, LispReader'READ_FINISHED)]
                (if (identical? form LispReader'READ_FINISHED)
                    (reverse z)
                    (recur (cons form z))
                )
            )
        )
    )

    (defn #_"unicode" StringReader'escape [#_"PushbackReader" r]
        (let [#_"Unicode" c (LispReader'read1 r)]
            (if (some? c)
                (cond
                    (= c Unicode'n)         Unicode'newline
                    (= c Unicode'backslash) c
                    (= c Unicode'quotation) c
                    'else (-/throw! "unsupported escape character \\" (-/-char c))
                )
                (-/throw! "EOF while reading string")
            )
        )
    )

    (defn #_"any" string-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (let [#_"StringBuilder" sb (-/StringBuilder'new)]
            (loop []
                (let [#_"Unicode" c (LispReader'read1 r)]
                    (if (some? c)
                        (when (not (= c Unicode'quotation))
                            (-/StringBuilder''append sb, (-/-char (if (= c Unicode'backslash) (StringReader'escape r) c)))
                            (recur)
                        )
                        (-/throw! "EOF while reading string")
                    )
                )
            )
            (-/StringBuilder''toString sb)
        )
    )

    (defn #_"any" discard-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (LispReader'read r, scope, nil, nil)
        r
    )

    (defn #_"any" quote-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (list (symbol! 'quote) (LispReader'read r, scope, nil, nil))
    )

    (declare LispReader'dispatchMacros)

    (defn #_"any" dispatch-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (let [#_"Unicode" c (LispReader'read1 r)]
            (if (some? c)
                (let [#_"fn" f'macro (get LispReader'dispatchMacros c)]
                    (if (some? f'macro)
                        (f'macro r scope c)
                        (do
                            (LispReader'unread r, c)
                            (-/throw! "no dispatch macro for " (-/-char c))
                        )
                    )
                )
                (-/throw! "EOF while reading character")
            )
        )
    )

    (defn #_"any" list-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (LispReader'readDelimitedForms r, scope, Unicode'rparen)
    )

    (defn #_"any" vector-reader [#_"PushbackReader" r, #_"seq" scope, #_"unicode" _delim]
        (LispReader'readDelimitedForms r, scope, Unicode'rbracket)
    )

    (defn #_"any" unmatched-delimiter-reader [#_"PushbackReader" _r, #_"seq" scope, #_"unicode" delim]
        (-/throw! "unmatched delimiter " (-/-char delim))
    )

    (def #_"map" LispReader'macros
        (cons-map
            Unicode'quotation   string-reader
            Unicode'apostrophe  quote-reader        Unicode'grave     quote-reader
            Unicode'lparen      list-reader         Unicode'rparen    unmatched-delimiter-reader
            Unicode'lbracket    vector-reader       Unicode'rbracket  unmatched-delimiter-reader
            Unicode'hash        dispatch-reader
        )
    )

    (def #_"map" LispReader'dispatchMacros
        (cons-map
            Unicode'underscore  discard-reader
        )
    )
)

(defn read [] (LispReader'read -/System'in, nil, nil, nil))
)

(defn repl []
    (let [esc (-/-char Unicode'escape)] (print (-/-str esc "[31mBeagle " esc "[32m=> " esc "[0m")))
    (flush)
    (-> (read) (eval) (prn))
    (#_recur repl)
)
