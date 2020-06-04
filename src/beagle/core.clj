(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* = aget apply aset char char? class conj defn doseq first fn fn? import int keys let map merge meta neg? next ns-imports ns-resolve ns-unmap number? object-array select-keys seq seq? seqable? some? str string? symbol symbol? the-ns var? var-get vary-meta when])
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

(refer! clojure.core [-> and cond cons defmacro identical? list memoize or time])

(defn throw! [& s] (throw (Error. (apply str s))))

(defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))

(defn #_"int" Integer'parseBinary [#_"String" s] (Integer/parseInt s, 2))

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

(def -=        =)
(def -apply    apply)
(def -char     char)
(def -char?    char?)
(def -conj     conj)
(def -first    first)
(def -fn?      fn?)
(def -int      int)
(def -neg?     neg?)
(def -next     next)
(def -number?  number?)
(def -seq      seq)
(def -seq?     seq?)
(def -seqable? seqable?)
(def -str      str)
(def -string?  string?)
(def -symbol   symbol)
(def -symbol?  symbol?)
(def -the-ns   the-ns)
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

(ns beagle.core
    (:refer-clojure :only [])
    (:require [beagle.bore :as -])
)

(-/import!)

(-/refer! beagle.bore [-> -= Appendable''append Flushable''flush Integer'parseBinary Matcher''matches Namespace''findInternedVar Pattern''matcher Pattern'compile PushbackReader''unread Reader''read StringBuilder''append StringBuilder''toString StringBuilder'new System'in System'out Var''-get -aget-0 -aget-1 -aget-2 and -anew-0 -anew-2 -anew-3 -apply -array? -aset-0! -aset-1! -aset-2! -char -char? cond -conj cons -first -fn? identical? -int list -neg? -next -number? or -seq -seq? -seqable? -str -string? -symbol -the-ns throw! -var? -volatile-acas-1! -volatile-aget-1 -volatile-aset-1!])

(-/defmacro about   [& s]   (-/cons 'do s))
(-/defmacro declare [x]     (-/list 'def x nil))
(-/defmacro when    [? & s] (-/list 'if ? (-/cons 'do s) nil))

(-/defmacro fn   [& s] (-/cons 'fn* s))
(-/defmacro let  [& s] (-/cons 'let* s))
(-/defmacro loop [& s] (-/cons 'loop* s))

(-/defmacro defn     [f & s] (-/list 'def f (-/cons 'fn s)))
(-/defmacro lazy-seq [& s]   (-/cons 'fn (-/cons [] s)))

(defn memoize  [x] x)
(defn -symbol? [x] false)

(def identical? -/identical?)

(defn identity [x] x)

(defn nil?   [x] (identical? x nil))
(defn true?  [x] (identical? x true))
(defn false? [x] (identical? x false))
(defn not    [x] (if x false true))
(defn some?  [x] (not (nil? x)))

(about #_"seq"
    (declare cons?)
    (declare Cons''seq)
    (declare closure?)
    (declare Closure''seq)

    (defn seq [s]
        (cond
            (nil? s)         nil
            (cons? s)       (Cons''seq s)
            (closure? s)    (Closure''seq s)
            (-/-seqable? s) (-/-seq s)
            (-/-fn? s)      (-/-apply s nil)
            'else           (-/throw! "seq not supported on " s)
        )
    )

    (declare Cons''first)

    (defn first [s]
        (let [s (seq s)]
            (cond
                (nil? s)     nil
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
                (nil? s)     nil
                (cons? s)   (Cons''next s)
                (-/-seq? s) (-/-next s)
                'else       (-/throw! "next not supported on " s)
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

(about #_"beagle.Atom"

(about #_"Atom"
    (defn #_"Atom" Atom'new [#_"any" init]
        (-> (-/-anew-2) (-/-aset-0! "Atom'meta") (-/-volatile-aset-1! init))
    )

    (declare =)

    (defn atom? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) "Atom'meta")))

    (defn #_"any" Atom''deref [#_"Atom" this]
        (-/-volatile-aget-1 this)
    )

    (declare apply)

    (defn #_"any" Atom''swap [#_"Atom" this, #_"fn" f, #_"seq" s]
        (loop []
            (let [#_"any" o (-/-volatile-aget-1 this) #_"any" o' (apply f o s)]
                (if (-/-volatile-acas-1! this o o') o' (recur))
            )
        )
    )

    (defn #_"any" Atom''reset [#_"Atom" this, #_"any" o']
        (-/-volatile-aset-1! this o')
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
        (-> (-/-anew-3) (-/-aset-0! "Cons'meta") (-/-aset-1! car) (-/-aset-2! cdr))
    )

    (defn cons? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) "Cons'meta")))

    (defn #_"any" Cons''car [#_"Cons" this] (when (cons? this) (-/-aget-1 this)))
    (defn #_"seq" Cons''cdr [#_"Cons" this] (when (cons? this) (-/-aget-2 this)))

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
        (nil? s)         nil
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
)

(about #_"beagle.ConsMap"

(about #_"ConsMap"
    (defn #_"ConsMap" ConsMap'new [#_"key" car, #_"value" cadr, #_"seq" cddr]
        (cons car (cons cadr cddr))
    )

    (defn #_"Cons" ConsMap''find [#_"ConsMap" this, #_"key" key]
        (some-kv (fn [#_"ConsMap" e] (when (= (first e) key) e)) this)
    )

    (defn #_"boolean" ConsMap''contains? [#_"ConsMap" this, #_"key" key]
        (some? (ConsMap''find this, key))
    )

    (defn #_"value" ConsMap''get [#_"ConsMap" this, #_"key" key]
        (second (ConsMap''find this, key))
    )

    (defn #_"ConsMap" ConsMap''assoc [#_"ConsMap" this, #_"key" key, #_"value" val]
        (if (and (#_= identical? (first this) key) (#_= identical? (second this) val))
            this
            (ConsMap'new key, val, this)
        )
    )

    (defn #_"seq" ConsMap''keys [#_"ConsMap" this]
        (lazy-seq
            (let [#_"seq" s (seq this)]
                (when (some? s)
                    (cons (first s) (ConsMap''keys (next (next s))))
                )
            )
        )
    )

    (defn #_"seq" ConsMap''vals [#_"ConsMap" this]
        (lazy-seq
            (let [#_"seq" s (seq this)]
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
        'else     (-/throw! "assoc not supported on " m)
    )
)

(defn cons-map [& kvs] (reduce-kv assoc nil kvs))

(defn contains? [m k]
    (cond
        (nil? m)   false
        (cons? m) (ConsMap''contains? m, k)
        'else     (-/throw! "contains? not supported on " m)
    )
)

(defn get [m k]
    (cond
        (nil? m)   nil
        (cons? m) (ConsMap''get m, k)
        'else     (-/throw! "get not supported on " m)
    )
)

(defn update [m k f & s] (assoc m k (apply f (get m k) s)))
)

(about #_"beagle.Symbol"

(about #_"Symbol"
    (defn #_"Symbol" Symbol'new [#_"String" ns, #_"String" name]
        (-> (-/-anew-3) (-/-aset-0! "Symbol'meta") (-/-aset-1! ns) (-/-aset-2! name))
    )

    (defn symbol? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) "Symbol'meta")))

    (defn #_"String" Symbol''ns   [#_"Symbol" this] (when (symbol? this) (-/-aget-1 this)))
    (defn #_"String" Symbol''name [#_"Symbol" this] (when (symbol? this) (-/-aget-2 this)))

    (declare Unicode'minus)
    (declare Unicode'slash)

    (defn #_"Symbol" Symbol'create [#_"String" name]
        (if (and (= (first name) Unicode'minus) (= (second name) Unicode'slash))
            (Symbol'new "-", (apply -/-str (next (next name))))
            (Symbol'new nil, name)
        )
    )

    (def Symbol'create (-/memoize Symbol'create))

    (defn #_"boolean" Symbol''equals [#_"Symbol" this, #_"any" that]
        (or (identical? this that)
            (and (symbol? that)
                (= (Symbol''ns this) (Symbol''ns that))
                (= (Symbol''name this) (Symbol''name that))
            )
        )
    )
)

(defn symbol! [s] (if (-/-symbol? s) (Symbol'create (-/-str s)) s))

(defn symbol [s] (cond (symbol? s) s (-/-symbol? s) (Symbol'create (-/-str s)) 'else (Symbol'create s)))
)

(about #_"unicode"
    (defn binary [s] (-/-char (-/Integer'parseBinary (if (-/-number? s) (-/-str s) (Symbol''name s)))))

    (def Unicode'newline    (binary    '1010))
    (def Unicode'escape     (binary   '11011))
    (def Unicode'space      (binary  '100000))
    (def Unicode'quotation  (binary  '100010))
    (def Unicode'hash       (binary  '100011))
    (def Unicode'apostrophe (binary  '100111))
    (def Unicode'lparen     (binary  '101000))
    (def Unicode'rparen     (binary  '101001))
    (def Unicode'comma      (binary  '101100))
    (def Unicode'minus      (binary  '101101))
    (def Unicode'slash      (binary  '101111))
    (def Unicode'lbracket   (binary '1011011))
    (def Unicode'backslash  (binary '1011100))
    (def Unicode'rbracket   (binary '1011101))
    (def Unicode'underscore (binary '1011111))
    (def Unicode'grave      (binary '1100000))
    (def Unicode'n          (binary '1101110))
)

(about #_"beagle.Closure"

(about #_"Closure"
    (defn #_"Closure" Closure'new [#_"FnExpr" fun, #_"map" env]
        (-> (-/-anew-3) (-/-aset-0! "Closure'meta") (-/-aset-1! fun) (-/-aset-2! env))
    )

    (defn closure? [x] (and (-/-array? x) (-/-= (-/-aget-0 x) "Closure'meta")))

    (defn #_"FnExpr" Closure''fun [#_"Closure" this] (when (closure? this) (-/-aget-1 this)))
    (defn #_"map"    Closure''env [#_"Closure" this] (when (closure? this) (-/-aget-2 this)))

    (declare Machine'compute)

    (defn #_"any" Closure''applyTo [#_"Closure" this, #_"seq" args]
        (let [
            #_"FnExpr" fun (Closure''fun this) #_"map" env (Closure''env this)
            env
                (let [#_"Symbol" x (second fun)]
                    (if (some? x) (assoc env x this) env)
                )
            env
                (loop [env env #_"seq" pars (seq (third fun)) args (seq args)]
                    (if (some? pars)
                        (recur (assoc env (first pars) (first args)) (next pars) (next args))
                        (let [#_"Symbol" x (fourth fun)]
                            (if (some? x) (assoc env x args) env)
                        )
                    )
                )
        ]
            (Machine'compute (fifth fun), env)
        )
    )

    (defn #_"seq" Closure''seq [#_"Closure" this]
        (Closure''applyTo this, nil)
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
        (identical? x y)                  true
        (or (nil? x) (nil? y) (true? x)  (true? y) (false? x) (false? y)) false
        (or (-/-string? x) (-/-char? x)) (-/-= x y)
        (or (symbol? x) (-/-symbol? x))  (Symbol''equals (symbol! x), (symbol! y))
        (or (symbol? y) (-/-symbol? y))  (Symbol''equals (symbol! y), (symbol! x))
        (cons? x)                        (Cons''equals x, y)
        (cons? y)                        (Cons''equals y, x)
        'else                            (-/throw! "= not supported on " x ", not even on " y)
    )
)
)

(about #_"append"
    (defn #_"char|String" escape-str [#_"char" c]
        (cond
            (= c Unicode'newline)   "\\n"
            (= c Unicode'quotation) "\\\""
            (= c Unicode'backslash) "\\\\"
            'else                   c
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
            (-/-string? x) (append-str a x)
            (symbol? x)    (append-sym a x)
            (cons? x)      (append-seq a x)
            (atom? x)      (-/Appendable''append a, "atom")
            (closure? x)   (-/Appendable''append a, "closure")
            (-/-symbol? x) (append-sym a (symbol! x))
            (-/-seq? x)    (-/Appendable''append a, "-seq")
            (-/-fn? x)     (-/Appendable''append a, "-fn")
            'else          (-/throw! "append not supported on " x)
        )
    )

    (defn #_"Appendable" append! [#_"Appendable" a, #_"any" x]
        (if (or (-/-string? x) (-/-char? x)) (-/Appendable''append a, x) (append a x))
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

    (defn space   [] (-/Appendable''append -/System'out, Unicode'space)   nil)
    (defn newline [] (-/Appendable''append -/System'out, Unicode'newline) nil)
    (defn flush   [] (-/Flushable''flush   -/System'out)                  nil)

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

(about #_"LiteralExpr"
    (def #_"LiteralExpr" LiteralExpr'NIL   (list 'literal-expr nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (list 'literal-expr true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (list 'literal-expr false))

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
                'else      (list 'literal-expr x)
            )
        )
    )
)

(about #_"IfExpr"
    (declare Compiler'analyze)

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
            (list 'if-expr test then else)
        )
    )
)

(about #_"InvokeExpr"
    (defn #_"Expr" InvokeExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"Expr" fexpr (Compiler'analyze (first form), scope)
            #_"Expr*" args (map (fn [%] (Compiler'analyze %, scope)) (next form))
        ]
            (list 'invoke-expr fexpr args)
        )
    )
)

(about #_"BodyExpr"
    (defn #_"Expr" BodyExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"Expr*" exprs (map (fn [%] (Compiler'analyze %, scope)) (next form))
        ]
            (list 'body-expr exprs)
        )
    )
)

(about #_"FnExpr"
    (defn #_"FnExpr" FnExpr'parse [#_"seq" form, #_"seq" scope]
        (let [
            #_"symbol?" self (symbol! (second form)) ? (symbol? self) self (when ? self) form (if ? (next (next form)) (next form))
            _
                (loop [pars nil etal nil #_"boolean" variadic? false #_"seq" s (seq (first form))]
                    (if (some? s)
                        (let [#_"symbol?" sym (symbol! (first s))]
                            (if (symbol? sym)
                                (if (nil? (Symbol''ns sym))
                                    (cond
                                        (= sym '&)
                                            (if (not variadic?)
                                                (recur pars etal true (next s))
                                                (-/throw! "overkill variadic parameter list")
                                            )
                                        (some? etal)
                                            (-/throw! "excess variadic parameter " sym)
                                        'else
                                            (if (not variadic?)
                                                (recur (cons sym pars) etal variadic? (next s))
                                                (recur           pars  sym  variadic? (next s))
                                            )
                                    )
                                    (-/throw! "can't use qualified name as parameter " sym)
                                )
                                (-/throw! "function parameters must be symbols")
                            )
                        )
                        (if (or (not variadic?) (some? etal))
                            (list (reverse pars) etal)
                            (-/throw! "missing variadic parameter")
                        )
                    )
                )
            #_"Symbol*" pars (first _) #_"Symbol" etal (second _)
            scope
                (loop [scope (if (some? self) (cons self scope) scope) #_"seq" s (seq pars)]
                    (if (some? s)
                        (recur (cons (first s) scope) (next s))
                        (if (some? etal) (cons etal scope) scope)
                    )
                )
            #_"Expr" body (BodyExpr'parse (cons 'do (next form)), scope)
        ]
            (list 'fn-expr self pars etal body)
        )
    )
)

(about #_"DefExpr"
    (def #_"map'" Beagle'ns (atom nil))

    (defn #_"Var" DefExpr'lookupVar [#_"Symbol" sym]
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

    (defn #_"Expr" DefExpr'parse [#_"seq" form, #_"seq" scope]
        (cond
            (nil? (next (next form)))         (-/throw! "too few arguments to def")
            (some? (next (next (next form)))) (-/throw! "too many arguments to def")
        )
        (let [#_"symbol?" s (symbol! (second form))]
            (if (symbol? s)
                (list 'def-expr (DefExpr'lookupVar s) (Compiler'analyze (third form), scope))
                (-/throw! "first argument to def must be a symbol")
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
            'fn         FnExpr'parse
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
            'let        (fn [a & s] (if (seq a) (list (list 'fn (list (first a)) (cons 'let (cons (next (next a)) s))) (second a)) (cons 'do s)))
            'loop       (fn [a & s] (cons (cons 'fn (cons 'recur (cons (ConsMap''keys a) s))) (ConsMap''vals a)))
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
        (or
            (when (and (nil? (Symbol''ns sym)) (some (fn [%] (= % sym)) scope))
                (list 'binding-expr sym)
            )
            (let [#_"any" o
                    (if (some? (Symbol''ns sym))
                        (-/Namespace''findInternedVar (-/-the-ns (-/-symbol "beagle.core")), (-/-symbol (Symbol''name sym)))
                        (get (deref Beagle'ns) sym)
                    )]
                (if (some? o)
                    (list 'var-expr o)
                    (-/throw! "unable to resolve symbol " sym)
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
            (or (symbol? form) (-/-symbol? form))                (Compiler'analyzeSymbol (symbol! form), scope)
            (or (cons? form) (and (-/-seq? form) (-/-seq form))) (Compiler'analyzeSeq form, scope)
            'else                                                (list 'literal-expr form)
        )
    )

    (defn #_"edn" Compiler'eval [#_"edn" form]
        (let [form (Compiler'macroexpand form)]
            (apply (Closure'new (Compiler'analyze (list 'fn [] form), nil), nil) nil)
        )
    )
)

(defn eval [form] (Compiler'eval form))
)

(about #_"machine"
    (defn #_"any" Machine'compute [#_"seq" form, #_"map" env]
        (let [f (first form) f'compute (fn [%] (Machine'compute %, env))]
            (cond
                (= f 'literal-expr) (second form)
                (= f 'binding-expr) (get env (second form))
                (= f 'var-expr)     (Var''get (second form))
                (= f 'if-expr)      (f'compute (if (f'compute (second form)) (third form) (fourth form)))
                (= f 'invoke-expr)  (apply (f'compute (second form)) (map f'compute (third form)))
                (= f 'body-expr)    (last (map f'compute (second form)))
                (= f 'fn-expr)      (Closure'new form, env)
                (= f 'def-expr)     (Var''bindRoot (second form), (f'compute (third form)))
                'else (-/throw! "Machine'compute not supported on " form)
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

    (def LispReader'naught (binary '11111))

    (defn #_"boolean" LispReader'isWhitespace [#_"unicode" c]
        (or (= c Unicode'space) (= c Unicode'comma) (= c Unicode'newline) (= c LispReader'naught))
    )

    (defn #_"Unicode" LispReader'read1 [#_"Reader" r]
        (let [#_"int" x (-/Reader''read r)]
            (when (not (-/-neg? x))
                (-/-char x)
            )
        )
    )

    (defn #_"void" LispReader'unread [#_"PushbackReader" r, #_"Unicode" c]
        (when (some? c)
            (-/PushbackReader''unread r, (-/-int c))
        )
        nil
    )

    (defn #_"String" LispReader'readToken [#_"PushbackReader" r, #_"unicode" c]
        (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, c)]
            (loop []
                (let [c (LispReader'read1 r)]
                    (if (or (nil? c) (LispReader'isWhitespace c) (LispReader'isTerminatingMacro c))
                        (do
                            (LispReader'unread r, c)
                            (-/StringBuilder''toString sb)
                        )
                        (do
                            (-/StringBuilder''append sb, c)
                            (recur)
                        )
                    )
                )
            )
        )
    )

    #_"\n !\"#%&'()*,-./0123456789=>?ABCDEFHILMNOPRSTUVWZ[\\]_abcdefghijklmnopqrstuvwxyz|"

    (def #_"Pattern" LispReader'rxSymbol (-/Pattern'compile "(-/)?[-a-zA-Z_0-9?!=&%][-a-zA-Z_0-9'*?!=>]*"))

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

    (def #_"any" LispReader'READ_FINISHED (-/-anew-0))

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
                    'else (-/throw! "unsupported escape character \\" c)
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
                            (-/StringBuilder''append sb, (if (= c Unicode'backslash) (StringReader'escape r) c))
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
        (list 'quote (LispReader'read r, scope, nil, nil))
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
                            (-/throw! "no dispatch macro for " c)
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
        (-/throw! "unmatched delimiter " delim)
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
    (let [esc Unicode'escape] (print (-/-str esc "[31mBeagle " esc "[32m=> " esc "[0m")))
    (flush)
    (-> (read) (eval) (prn))
    (#_recur repl)
)
