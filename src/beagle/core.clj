(ns beagle.core
    (:refer-clojure :only []) (:require [clojure.core :as -])
)

(-/defmacro § [& _])
(-/defmacro ß [& _])

(ns beagle.bore
    (:refer-clojure :only [= cons defmacro defn doseq first keys let map meta or reduce symbol? var-get vary-meta]) (:require [clojure.core :as -])
)

(defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (-/ns-imports -/*ns*))] (-/ns-unmap -/*ns* n#)) (-/import ~@syms-or-seqs)))

(import!
    [java.lang Appendable Character Class Error Integer Long Number Object String StringBuilder System]
    [java.lang.reflect Array Constructor]
    [java.io Flushable PrintWriter PushbackReader Reader]
    [java.util.regex Matcher Pattern]
    [clojure.lang Associative Counted DynamicClassLoader IHashEq ILookup IMeta IObj IPersistentCollection IPersistentMap Keyword Namespace Seqable Var]
    [beagle.util.concurrent.atomic AtomicReference]
)

(defmacro refer! [ns s]
    (let [f #(let [v (-/ns-resolve (-/the-ns (if (= ns '-) 'clojure.core ns)) %) n (vary-meta % -/merge (-/select-keys (meta v) [:dynamic :macro]))] `(def ~n ~(var-get v)))]
        (if (symbol? s) (f s) (cons 'do (map f s)))
    )
)

(defn throw! [#_"String" s] (throw (Error. s)))

(defmacro about [& s] (cons 'do s))

(about #_"Numbers"
    (refer! - [< <= > >= int neg? pos? zero?])

    (defn int! [^Number n] (.intValue n))

    (defn +
        ([] (int 0))
        ([x] (int! x))
        ([x y] (-/unchecked-add-int (int! x) (int! y)))
        ([x y & s] (reduce + (+ x y) s))
    )

    (defn -
        ([x] (-/unchecked-negate-int (int! x)))
        ([x y] (-/unchecked-subtract-int (int! x) (int! y)))
        ([x y & s] (reduce - (- x y) s))
    )

    (def inc -/unchecked-inc-int)
    (def dec -/unchecked-dec-int)

    (defn bit-and [x y] (int! (-/bit-and x y)))

    (def & bit-and)

    (defn << [x y] (int! (-/bit-shift-left x y)))
    (defn >> [x y] (int! (-/bit-shift-right x y)))
)

(about #_"java.lang"

(about #_"Appendable"
    (defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))
)

(about #_"Character"
    (defn char? [x] (-/instance? Character x))

    (defn #_"int"       Character'digit        [#_"char" ch, #_"int" radix] (Character/digit ch, radix))
    (defn #_"boolean"   Character'isWhitespace [#_"char" ch]                (Character/isWhitespace ch))
    (defn #_"Character" Character'valueOf      [#_"char" ch]                (Character/valueOf ch))
)

(about #_"Integer"
    (defn int? [x] (or (-/instance? Integer x) (-/instance? Long x)))

    (defn #_"int"     Integer'parseInt [#_"String" s] (Integer/parseInt s))
    (defn #_"Integer" Integer'valueOf  [#_"int" i]    (Integer/valueOf i))
)

(about #_"Number"
    (defn number? [x] (-/instance? Number x))

    (defn #_"String" Number''toString [^Number this] (.toString this))
)

(about #_"Object"
    (def Object'array (Class/forName "[Ljava.lang.Object;"))

    (defn #_"String" Object''toString [^Object this] (.toString this))
)

(about #_"String"
    (defn string? [x] (-/instance? String x))

    (defn #_"char"    String''charAt     [^String this, #_"int" i]    (.charAt this, i))
    (defn #_"boolean" String''endsWith   [^String this, #_"String" s] (.endsWith this, s))
    (defn #_"int"     String''indexOf   ([^String this, #_"int" ch]   (.indexOf this, ch))     ([^String this, #_"String" s, #_"int" from] (.indexOf this, s, from)))
    (defn #_"String"  String''intern     [^String this]               (.intern this))
    (defn #_"int"     String''length     [^String this]               (.length this))
    (defn #_"boolean" String''startsWith [^String this, #_"String" s] (.startsWith this, s))
    (defn #_"String"  String''substring ([^String this, #_"int" from] (.substring this, from)) ([^String this, #_"int" from, #_"int" over] (.substring this, from, over)))
)

(about #_"StringBuilder"
    (defn #_"StringBuilder" StringBuilder'new [] (StringBuilder.))

    (defn #_"StringBuilder" StringBuilder''append   [^StringBuilder this, #_"char" ch] (.append this, ch))
    (defn #_"String"        StringBuilder''toString [^StringBuilder this]              (.toString this))
)

(about #_"System"
    (defn #_"void" System'arraycopy [#_"array" a, #_"int" i, #_"array" b, #_"int" j, #_"int" n] (System/arraycopy a, i, b, j, n))
)
)

(about #_"java.lang.reflect"

(about #_"Array"
    (defn array? [x] (.isArray (-/class x)))

    (defn #_"any" Array'get       [#_"array" a, #_"int" i] (Array/get a, i))
    (defn #_"int" Array'getLength [#_"array" a]            (Array/getLength a))
)
)

(about #_"java.io"

(about #_"Flushable"
    (defn #_"void" Flushable''flush [^Flushable this] (.flush this))
)

(about #_"PrintWriter"
    (defn #_"void" PrintWriter''println [^PrintWriter this, #_"String" s] (.println this, s))
)

(about #_"PushbackReader"
    (defn #_"void" PushbackReader''unread [^PushbackReader this, #_"int" x] (.unread this, x))
)

(about #_"Reader"
    (defn #_"int" Reader''read [^Reader this] (.read this))
)
)

(about #_"java.util.regex"

(about #_"Pattern"
    (defn pattern? [x] (-/instance? Pattern x))

    (defn #_"Pattern" Pattern'compile  [#_"String" s]                (Pattern/compile s))
    (defn #_"Matcher" Pattern''matcher [^Pattern this, #_"String" s] (.matcher this, s))
    (defn #_"String"  Pattern''pattern [^Pattern this]               (.pattern this))
)

(about #_"Matcher"
    (defn matcher? [x] (-/instance? Matcher x))

    (defn #_"String"  Matcher''group     ([^Matcher this] (.group this)) ([^Matcher this, #_"int" n] (.group this, n)))
    (defn #_"int"     Matcher''groupCount [^Matcher this] (.groupCount this))
    (defn #_"boolean" Matcher''matches    [^Matcher this] (.matches this))
)
)

(about #_"clojure.lang"

(about #_"Compiler"
    (def #_"var" Compiler'LOADER clojure.lang.Compiler/LOADER)
)

(about #_"DynamicClassLoader"
    (defn #_"Class" DynamicClassLoader''defineClass [^DynamicClassLoader this, #_"String" name, #_"byte[]" bytes, #_"form" _] (.defineClass this, name, bytes, _))
)

(about #_"ILookup"
    (defn clojure-ilookup? [x] (-/instance? clojure.lang.ILookup x))

    (defn #_"value" ILookup''valAt ([^ILookup this, #_"key" key] (.valAt this, key)) ([^ILookup this, #_"key" key, #_"value" not-found] (.valAt this, key, not-found)))
)

(about #_"Keyword"
    (defn clojure-keyword? [x] (-/instance? clojure.lang.Keyword x))

    (defn #_"Symbol" Keyword''sym [^Keyword this] (.sym this))
)

(about #_"Namespace"
    (defn clojure-namespace? [x] (-/instance? clojure.lang.Namespace x))

    (defn #_"map"    Namespace''-getMappings     [^Namespace this]                  (.getMappings this))
    (defn #_"Object" Namespace''-getMapping      [^Namespace this, #_"Symbol" name] (.getMapping this, name))
    (defn #_"var"    Namespace''-intern          [^Namespace this, #_"Symbol" sym]  (.intern this, sym))
    (defn #_"var"    Namespace''-findInternedVar [^Namespace this, #_"Symbol" name] (.findInternedVar this, name))
)

(about #_"Symbol"
    (defn clojure-symbol? [x] (-/instance? clojure.lang.Symbol x))
)

(about #_"Var"
    (defn clojure-var? [x] (-/instance? clojure.lang.Var x))

    (defn #_"Object"  Var''-alterRoot [^Var this, #_"IFn" fn, #_"ISeq" args] (.alterRoot this, fn, args))
    (defn #_"boolean" Var''-hasRoot   [^Var this]                            (.hasRoot this))
    (defn #_"boolean" Var''-isBound   [^Var this]                            (.isBound this))
    (defn #_"Object"  Var''-get       [^Var this]                            (.get this))
)
)

(about #_"beagle.util.concurrent.atomic"

(about #_"AtomicReference"
    (defn #_"AtomicReference" AtomicReference'new [#_"any" init] (AtomicReference. init))

    (defn #_"boolean" AtomicReference''compareAndSet [^AtomicReference this, #_"any" x, #_"any" y] (.compareAndSet this, x, y))
    (defn #_"any"     AtomicReference''get           [^AtomicReference this]                       (.get this))
    (defn #_"void"    AtomicReference''set           [^AtomicReference this, #_"any" x]            (.set this, x))
)
)

(defn identical? [a b] (-/identical? a b))

(defn A'new [n] (-/object-array n))

(defn A'clone  [^"[Ljava.lang.Object;" a]     (-/aclone a))
(defn A'get    [^"[Ljava.lang.Object;" a i]   (-/aget a i))
(defn A'length [^"[Ljava.lang.Object;" a]     (-/alength a))
(defn A'set    [^"[Ljava.lang.Object;" a i x] (-/aset a i x))

(defn new* [^Class c & s] (.newInstance ^Constructor (first (.getConstructors c)), (A'new s)))

(defn M'get ([m k] (-/get m k)) ([m k not-found] (-/get m k not-found)))

(about #_"beagle.Mutable"
    (defn #_"Mutable" Mutable''mutate! [#_"Mutable" this, #_"key" key, #_"value" val] (.mutate this, key, val))
)

(about #_"beagle.Typed"
    (defn #_"type" Typed''type [#_"Typed" this] (.type this))
)

(ns beagle.core
    (:refer-clojure :only [boolean char satisfies?]) (:require [clojure.core :as -])
    (:refer beagle.bore :only
        [
            about import! int int! refer! throw!
            Appendable''append
            char? Character'digit Character'isWhitespace Character'valueOf
            int? Integer'parseInt Integer'valueOf
            number? Number''toString
            Object'array Object''toString
            string? String''charAt String''endsWith String''indexOf String''intern String''length String''startsWith String''substring
            StringBuilder'new StringBuilder''append StringBuilder''toString
            System'arraycopy
            array? Array'get Array'getLength
            Flushable''flush
            PrintWriter''println
            PushbackReader''unread
            Reader''read
            pattern? Pattern'compile Pattern''matcher Pattern''pattern
            matcher? Matcher''group Matcher''groupCount Matcher''matches
            Compiler'LOADER
            DynamicClassLoader''defineClass
            clojure-ilookup? ILookup''valAt
            clojure-keyword? Keyword''sym
            clojure-namespace? Namespace''-getMappings Namespace''-getMapping Namespace''-intern Namespace''-findInternedVar
            clojure-symbol?
            clojure-var? Var''-alterRoot Var''-hasRoot Var''-isBound Var''-get
            AtomicReference'new AtomicReference''compareAndSet AtomicReference''get AtomicReference''set
            identical?
            A'new A'clone A'get A'length A'set new* M'get
            Mutable''mutate! Typed''type
        ]
    )
)

(import!)

(refer! - [= alter-var-root conj cons count defmacro defn defonce even? first fn interleave keyword keyword? let list list* loop map mapcat meta next not= nth odd? partial partition second seq seq? split-at str symbol symbol? var-get vary-meta vec vector vector? with-meta])
(refer! beagle.bore [& + - < << <= > >= >> dec inc neg? pos? zero?])

(defmacro case! [e & clauses] (if (odd? (count clauses)) `(condp = ~e ~@clauses) `(condp = ~e ~@clauses (throw! (str ~e " is definitely not that case!")))))

(let [last-id' (-/atom 0)] (defn next-id! [] (-/swap! last-id' inc)))

(defn gensym
    ([] (gensym "G__"))
    ([prefix] (-/symbol (str prefix (next-id!))))
)

(defmacro declare [& names] `(do ~@(map #(list 'def (vary-meta % -/assoc :declared true)) names)))

(defn identity   [x] x)

(defn nil?   [x] (identical? x nil))
(defn not    [x] (if x false true))
(defn some?  [x] (not (nil? x)))

(defmacro if-not
    ([? then] (if-not ? then nil))
    ([? then else] (list 'if ? else then))
)

(defmacro and
    ([] true)
    ([x] x)
    ([x & s] `(let [and# ~x] (if and# (and ~@s) and#)))
)

(defmacro or
    ([] nil)
    ([x] x)
    ([x & s] `(let [or# ~x] (if or# or# (or ~@s))))
)

(defmacro any
    ([f x y] `(~f ~x ~y))
    ([f x y & s] `(let [f# ~f x# ~x] (or (f# x# ~y) (any f# x# ~@s))))
)

(defmacro letfn [fnspecs & body]
    `(letfn* ~(vec (interleave (map first fnspecs) (map #(cons `fn %) fnspecs))) ~@body)
)

(letfn [(=> [s] (if (= '=> (first s)) (next s) (cons nil s)))]
    (defmacro     when       [? & s] (let [[e & s] (=> s)]               `(if     ~? (do ~@s) ~e)))
    (defmacro     when-not   [? & s] (let [[e & s] (=> s)]               `(if-not ~? (do ~@s) ~e)))
    (defmacro let-when     [v ? & s] (let [[e & s] (=> s)] `(let ~(vec v) (if     ~? (do ~@s) ~e))))
    (defmacro let-when-not [v ? & s] (let [[e & s] (=> s)] `(let ~(vec v) (if-not ~? (do ~@s) ~e))))
)

(defmacro cond [& s]
    (when s
        `(if ~(first s)
            ~(when (next s) => (throw! "cond requires an even number of forms")
                (second s)
            )
            (cond ~@(next (next s)))
        )
    )
)

(defmacro if-let
    ([bind then] `(if-let ~bind ~then nil))
    ([bind then else & _]
        `(let-when [x# ~(bind 1)] x# ~'=> ~else
            (let [~(bind 0) x#]
                ~then
            )
        )
    )
)

(defmacro if-some
    ([bind then] `(if-some ~bind ~then nil))
    ([bind then else & _]
        `(let-when [x# ~(bind 1)] (some? x#) ~'=> ~else
            (let [~(bind 0) x#]
                ~then
            )
        )
    )
)

(defmacro if-first
    ([bind then] `(if-first ~bind ~then nil))
    ([bind then else & _]
        `(let-when [s# (seq ~(bind 1))] (some? s#) ~'=> ~else
            (let [~(bind 0) (first s#)]
                ~then
            )
        )
    )
)

(letfn [(=> [s] (if (= '=> (first s)) (next s) (cons nil s)))]
    (defmacro when-let   [v & s] (let [[e & s] (=> s)] `(if-let   ~(vec v) (do ~@s) ~e)))
    (defmacro when-some  [v & s] (let [[e & s] (=> s)] `(if-some  ~(vec v) (do ~@s) ~e)))
    (defmacro when-first [v & s] (let [[e & s] (=> s)] `(if-first ~(vec v) (do ~@s) ~e)))
)

(defmacro condp [f? expr & clauses]
    (let [gpred (gensym "pred__") gexpr (gensym "expr__")
          emit-
            (fn emit- [f? expr args]
                (let [[[a b c :as clause] more] (split-at (if (= :>> (second args)) 3 2) args) n (count clause)]
                    (cond
                        (= 0 n) `(throw! (str "no matching clause: " ~expr))
                        (= 1 n) a
                        (= 2 n) `(if (~f? ~a ~expr)
                                    ~b
                                    ~(emit- f? expr more)
                                )
                        :else   `(if-let [p# (~f? ~a ~expr)]
                                    (~c p#)
                                    ~(emit- f? expr more)
                                )
                    )
                )
            )]
        `(let [~gpred ~f? ~gexpr ~expr]
            ~(emit- gpred gexpr clauses)
        )
    )
)

(letfn [(v' [v] (cond (vector? v) v (symbol? v) [v v] :else [`_# v]))
        (r' [r] (cond (vector? r) `((recur ~@r)) (some? r) `((recur ~r))))
        (=> [s] (if (= '=> (first s)) (next s) (cons nil s)))
        (l' [v ? r s] (let [r (r' r) [e & s] (=> s)] `(loop ~(v' v) (if ~? (do ~@s ~@r) ~e))))]
    (defmacro loop-when [v ? & s] (l' v ? nil s))
    (defmacro loop-when-recur [v ? r & s] (l' v ? r s))
)

(letfn [(r' [r] (cond (vector? r) `(recur ~@r) (some? r) `(recur ~r)))
        (=> [s] (if (= '=> (first s)) (second s)))]
    (defmacro recur-when [? r & s] `(if ~? ~(r' r) ~(=> s)))
)

(defmacro doseq [bindings & body]
    (letfn [(emit- [e r]
                (when e => [`(do ~@body) true]
                    (let [[k v & e] e]
                        (if (keyword? k)
                            (let [[f r?] (emit- e r)]
                                (case! k
                                    :let   [`(let ~v ~f) r?]
                                    :while [`(when ~v ~f ~@(when r? [r])) false]
                                    :when  [`(if ~v (do ~f ~@(when r? [r])) ~r) false]
                                )
                            )
                            (let [s (gensym "s__") r `(recur (next ~s)) [f r?] (emit- e r)]
                                [`(loop-when [~s (seq ~v)] ~s (let [~k (first ~s)] ~f ~@(when r? [r]))) true]
                            )
                        )
                    )
                )
            )]
        (first (emit- (seq bindings) nil))
    )
)

(defmacro -> [x & s]
    (when s => x
        (recur &form &env
            (let-when [f (first s)] (seq? f) => (list f x)
                (with-meta `(~(first f) ~x ~@(next f)) (meta f))
            )
            (next s)
        )
    )
)

(about #_"defp, defq, defr, defm"

(about #_"defproto"

#_bore!
(defn gen-interface* [sym]
    (DynamicClassLoader''defineClass (var-get Compiler'LOADER), (str sym), (second (#'-/generate-interface (-/hash-map (-/keyword (-/name :name)) sym))), nil)
)

(defn emit-defproto* [name sigs]
    (let [
        iname (-/symbol (str (-/munge (-/namespace-munge -/*ns*)) "." (-/munge name)))
    ]
        `(do
            #_bore!
            (defonce ~name (-/hash-map)) #_alt #_(declare ~name) #_(refer* '~name)
            #_bore!
            (gen-interface* '~iname)
            (alter-var-root (var ~name) -/merge
                ~(-/hash-map :var (list 'var name), :on (list 'quote iname), :on-interface (list `-/resolve (list 'quote iname)))
            )
            ~@(map (fn [[f & _]] `(defmacro ~f [x# & s#] (list* (list -/find-protocol-method '~name ~(-/keyword (str f)) x#) x# s#))) sigs)
            '~name
        )
    )
)

(defmacro defproto [name & sigs]
    (emit-defproto* name sigs)
)
)

#_bore!
(defn parse-opts [s]
    (loop-when-recur [opts {} [k v & rs :as s] s] (keyword? k) [(-/assoc opts k v) rs] => [opts s])
)

#_bore!
(refer! - [take-while drop-while])

#_bore!
(defn parse-impls [specs]
    (loop-when-recur [impls {} s specs] (seq s) [(-/assoc impls (first s) (take-while seq? (next s))) (drop-while seq? (next s))] => impls)
)

#_bore!
(refer! - [#_var? complement resolve deref keys maybe-destructured apply concat vals])

#_bore!
(defn parse-opts+specs [opts+specs]
    (let [
        [opts specs] (parse-opts opts+specs)
        impls        (parse-impls specs)
        interfaces   (-> (map #(if (#_var? (complement -/class?) (resolve %)) (:on (deref (resolve %))) %) (keys impls)) -/set (-/disj 'Object 'java.lang.Object) vec)
        methods      (map (fn [[name params & body]] (-/cons name (maybe-destructured params body))) (apply concat (vals impls)))
    ]
        [interfaces methods opts]
    )
)

(about #_"beagle.Mutable"
    #_bore!
    (defonce Mutable (-/hash-map)) #_alt #_(refer* 'Mutable)
    #_bore!
    (DynamicClassLoader''defineClass (var-get Compiler'LOADER), "beagle.core.Mutable", (second (#'-/generate-interface (-/hash-map (-/keyword (-/name :name)) 'beagle.core.Mutable, (-/keyword (-/name :methods)) '[[mutate [java.lang.Object java.lang.Object] java.lang.Object nil]]))), nil)
    (alter-var-root #'Mutable -/merge (-/hash-map :var #'Mutable, :on 'beagle.core.Mutable, :on-interface (-/resolve (-/symbol "beagle.core.Mutable"))))

    (defn mutable? [x] (satisfies? Mutable x))
)

(about #_"beagle.Typed"
    #_bore!
    (defonce Typed (-/hash-map)) #_alt #_(refer* 'Typed)
    #_bore!
    (DynamicClassLoader''defineClass (var-get Compiler'LOADER), "beagle.core.Typed", (second (#'-/generate-interface (-/hash-map (-/keyword (-/name :name)) 'beagle.core.Typed, (-/keyword (-/name :methods)) '[[type [] java.lang.Object nil]]))), nil)
    (alter-var-root #'Typed -/merge (-/hash-map :var #'Typed, :on 'beagle.core.Typed, :on-interface (-/resolve (-/symbol "beagle.core.Typed"))))

    (defn typed? [x] (satisfies? Typed x))
)

(about #_"defarray"

#_bore!
(defn emit-defarray* [tname cname fields interfaces methods opts]
    (let [
        classname  (-/with-meta (-/symbol (str (-/namespace-munge -/*ns*) "." cname)) (meta cname))
        interfaces (vec interfaces)
        fields     (map #(with-meta % nil) fields)
    ]
        (let [a '__array s (mapcat (fn [x y] [(-/name #_keyword y) x]) (-/range) fields)]
            (letfn [(ilookup [[i m]]
                        [
                            (conj i 'clojure.lang.ILookup)
                            (conj m
                                `(valAt [this# k#] (ILookup''valAt this# k# nil))
                                `(valAt [this# k# else#] (if-some [x# (case! (-/name k#) ~@s nil)] (#_A'get -/aget (. this# ~a) x#) else#))
                            )
                        ]
                    )
                    (mutable [[i m]]
                        [
                            (conj i 'beagle.core.Mutable)
                            (conj m
                                `(mutate [this# k# v#] (let [x# (case! (-/name k#) ~@s)] (#_A'set -/aset (. this# ~a) x# v#) this#))
                            )
                        ]
                    )
                    (typed [[i m]]
                        [
                            (conj i 'beagle.core.Typed)
                            (conj m
                                `(type [this#] '~classname)
                            )
                        ]
                    )]
                (let [[i m] (-> [interfaces methods] ilookup mutable typed)]
                    `(-/eval '~(-/read-string (str (list* 'deftype* (symbol (-/name (-/ns-name -/*ns*)) (-/name tname)) classname (vector a) :implements (vec i) m))))
                )
            )
        )
    )
)

#_bore!
(defmacro defarray [name fields & opts+specs] #_alt #_`(refer* '~name)
    (let [[interfaces methods opts] (parse-opts+specs opts+specs)]
        `(do
            ~(emit-defarray* name name (vec fields) (vec interfaces) methods opts)
            (-/eval '~(-/list (-/symbol "clojure.core/import*") (str (-/namespace-munge -/*ns*) "." name)))
        )
    )
)
)

(about #_"defassoc"

#_bore!
(defn emit-defassoc* [tname cname interfaces methods opts]
    (let [
        classname  (-/with-meta (-/symbol (str (-/namespace-munge -/*ns*) "." cname)) (meta cname))
        interfaces (vec interfaces)
    ]
        (let [a '__assoc]
            (letfn [(eqhash [[i m]]
                        [
                            (conj i 'clojure.lang.IHashEq)
                            (conj m
                                `(equals [this# that#] (and #_(some? that#) (-/instance? ~tname that#) (.equals (. this# ~a) (. that# ~a))))
                            )
                        ]
                    )
                    (iobj [[i m]]
                        [
                            (conj i 'clojure.lang.IObj)
                            (conj m
                                `(meta [this#] (.meta (. this# ~a)))
                                `(withMeta [this# m#] (new ~tname (.withMeta (. this# ~a) m#)))
                            )
                        ]
                    )
                    (ilookup [[i m]]
                        [
                            (conj i 'clojure.lang.ILookup)
                            (conj m
                                `(valAt [this# k#] (.valAt this# k# nil))
                                `(valAt [this# k# else#] (.valAt (. this# ~a) k# else#))
                            )
                        ]
                    )
                    (imap [[i m]]
                        [
                            (conj i 'clojure.lang.IPersistentMap)
                            (conj m
                                `(count [this#] (.count (. this# ~a)))
                                `(empty [this#] (new ~tname (.empty (. this# ~a))))
                                `(cons [this# e#] (new ~tname (.cons (. this# ~a) e#)))
                                `(equiv [this# that#]
                                    (or (identical? this# that#)
                                        (and (identical? (-/class this#) (-/class that#))
                                            (= (. this# ~a) (. that# ~a))
                                        )
                                    )
                                )
                                `(containsKey [this# k#] (.containsKey (. this# ~a) k#))
                                `(entryAt [this# k#] (.entryAt (. this# ~a) k#))
                                `(seq [this#] (.seq (. this# ~a)))
                                `(assoc [this# k# v#] (new ~tname (.assoc (. this# ~a) k# v#)))
                                `(without [this# k#] (new ~tname (.without (. this# ~a) k#)))
                            )
                        ]
                    )
                    (typed [[i m]]
                        [
                            (conj i 'beagle.core.Typed)
                            (conj m
                                `(type [this#] '~classname)
                            )
                        ]
                    )]
                (let [[i m] (-> [interfaces methods] eqhash iobj ilookup imap typed)]
                    `(-/eval '~(-/read-string (str (list* 'deftype* (symbol (-/name (-/ns-name -/*ns*)) (-/name tname)) classname (vector a) :implements (vec i) m))))
                )
            )
        )
    )
)

#_bore!
(defmacro defassoc [name & opts+specs] #_alt #_`(refer* '~name)
    (let [[interfaces methods opts] (parse-opts+specs opts+specs)]
        `(do
            ~(emit-defassoc* name name (vec interfaces) methods opts)
            (-/eval '~(-/list (-/symbol "clojure.core/import*") (str (-/namespace-munge -/*ns*) "." name)))
        )
    )
)
)

(about #_"extend"

(defn extend [atype & proto+mmaps]
    (doseq [[proto mmap] (partition 2 proto+mmaps)]
        (when-not (#'-/protocol? proto)
            (throw! (str proto " is not a protocol"))
        )
        (when (#'-/implements? proto atype)
            (throw! (str atype " already directly implements " (:on-interface proto) " for protocol " (:var proto)))
        )
        (alter-var-root (:var proto) -/assoc-in [:impls atype] mmap)
    )
)

(defn emit-impl* [_ [p fs]]
    [p (-/zipmap (map #(-> % first -/name -/keyword) fs) (map #(let [% (next %)] (if (= '=> (first %)) (second %) (cons `fn %))) fs))]
)

(defmacro extend-type [t & specs]
    `(extend ~t ~@(mapcat (partial emit-impl* t) (#'-/parse-impls specs)))
)
)

(defmacro defp [p & s]                                      `(do (defproto ~p ~@s)             '~p))
(defmacro defq [r f & s] (let [c (-/symbol (str r "'class"))] `(do (defarray ~c ~(vec f) ~r ~@s) '~c)))
(defmacro defr [r]       (let [c (-/symbol (str r "'class"))] `(do (defassoc ~c ~r)              '~c)))
(defmacro defm [r & s]   (let [i `(:on-interface ~r)]       `(do (extend-type ~i ~@s)          ~i)))
)

(about #_"beagle.Seqable"
    (defp Seqable
        (#_"seq" Seqable'''seq [#_"Seqable" this])
    )

    (-/extend-protocol Seqable clojure.lang.Seqable
        (Seqable'''seq [x] (.seq x))
    )

    (defn seqable? [x] (satisfies? Seqable x))

    (defn #_"seq" seq [x] (when (some? x) (Seqable'''seq x)))

    (defn empty? [x] (not (seq x)))
)

(about #_"beagle.ISeq"
    (defp ISeq
        (#_"Object" ISeq'''first [#_"seq" this])
        (#_"seq" ISeq'''next [#_"seq" this])
    )

    (-/extend-protocol ISeq clojure.lang.ISeq
        (ISeq'''first [s] (.first s))
        (ISeq'''next [s] (.next s))
    )

    (defn seq? [x] (satisfies? ISeq x))

    (defn first [s] (if (seq? s) (ISeq'''first s) (when-some [s (seq s)] (ISeq'''first s))))

    (defn #_"seq" next [s] (if (seq? s) (ISeq'''next s) (when-some [s (seq s)] (ISeq'''next s))))

    (defn second [s] (first (next s)))
    (defn third  [s] (first (next (next s))))
    (defn fourth [s] (first (next (next (next s)))))
    (defn last   [s] (if-some [r (next s)] (recur r) (first s)))
)

(about #_"beagle.IObject"
    (defp IObject
        (#_"boolean" IObject'''equals [#_"IObject" this, #_"Object" that])
    )

    (-/extend-protocol IObject java.lang.Object
        (IObject'''equals [this, that] (.equals this, that))
    )
)

(about #_"beagle.IAppend"
    (defp IAppend
        (#_"Appendable" IAppend'''append [#_"IAppend" this, #_"Appendable" a])
    )
)

(about #_"beagle.Counted"
    (defp Counted
        (#_"int" Counted'''count [#_"Counted" this])
    )

    (-/extend-protocol Counted
        clojure.lang.Counted   (Counted'''count [o] (.count o))
        java.lang.CharSequence (Counted'''count [s] (.length s))
    )

    (-/extend-protocol Counted
        (do Object'array) (Counted'''count [a] (Array'getLength a))
    )

    (defn counted? [x] (satisfies? Counted x))

    (defn count
        ([x] (count x -1))
        ([x m]
            (cond
                (nil? x)
                    0
                (counted? x)
                    (Counted'''count x)
                (seqable? x)
                    (loop-when [n 0 s (seq x)] (and (some? s) (or (neg? m) (< n m))) => n
                        (when (counted? s) => (recur (inc n) (next s))
                            (+ n (Counted'''count s))
                        )
                    )
                :else
                    (throw! (str "count not supported on " x))
            )
        )
    )
)

(about #_"beagle.IFn"
    (defp IFn
        (#_"Object" IFn'''invoke
            [#_"fn" this]
            [#_"fn" this, a1]
            [#_"fn" this, a1, a2]
            [#_"fn" this, a1, a2, a3]
            [#_"fn" this, a1, a2, a3, a4]
            [#_"fn" this, a1, a2, a3, a4, a5]
            [#_"fn" this, a1, a2, a3, a4, a5, a6]
            [#_"fn" this, a1, a2, a3, a4, a5, a6, a7]
            [#_"fn" this, a1, a2, a3, a4, a5, a6, a7, a8]
            [#_"fn" this, a1, a2, a3, a4, a5, a6, a7, a8, a9]
            [#_"fn" this, a1, a2, a3, a4, a5, a6, a7, a8, a9, #_"seq" args]
        )
        (#_"Object" IFn'''applyTo [#_"fn" this, #_"seq" args])
    )

    (declare anew)

    (-/extend-protocol IFn clojure.lang.IFn
        (IFn'''invoke
            ([this]                                                   (.invoke this))
            ([this, a1]                                               (.invoke this, a1))
            ([this, a1, a2]                                           (.invoke this, a1, a2))
            ([this, a1, a2, a3]                                       (.invoke this, a1, a2, a3))
            ([this, a1, a2, a3, a4]                                   (.invoke this, a1, a2, a3, a4))
            ([this, a1, a2, a3, a4, a5]                               (.invoke this, a1, a2, a3, a4, a5))
            ([this, a1, a2, a3, a4, a5, a6]                           (.invoke this, a1, a2, a3, a4, a5, a6))
            ([this, a1, a2, a3, a4, a5, a6, a7]                       (.invoke this, a1, a2, a3, a4, a5, a6, a7))
            ([this, a1, a2, a3, a4, a5, a6, a7, a8]                   (.invoke this, a1, a2, a3, a4, a5, a6, a7, a8))
            ([this, a1, a2, a3, a4, a5, a6, a7, a8, a9]               (.invoke this, a1, a2, a3, a4, a5, a6, a7, a8, a9))
            ([this, a1, a2, a3, a4, a5, a6, a7, a8, a9, #_"seq" args] (.invoke this, a1, a2, a3, a4, a5, a6, a7, a8, a9, (anew args)))
        )
        (IFn'''applyTo [this, args] (.applyTo this, args))
    )

    (defn ifn? [x] (satisfies? IFn x))

    (declare cons)

    (defn spread [s]
        (cond
            (nil? s) nil
            (nil? (next s)) (seq (first s))
            :else (cons (first s) (spread (next s)))
        )
    )

    (defn list*
        ([s] (seq s))
        ([a s] (cons a s))
        ([a b s] (cons a (cons b s)))
        ([a b c s] (cons a (cons b (cons c s))))
        ([a b c d & s] (cons a (cons b (cons c (cons d (spread s))))))
    )

    (defn apply
        ([#_"fn" f s] (IFn'''applyTo f, (seq s)))
        ([#_"fn" f a s] (IFn'''applyTo f, (list* a s)))
        ([#_"fn" f a b s] (IFn'''applyTo f, (list* a b s)))
        ([#_"fn" f a b c s] (IFn'''applyTo f, (list* a b c s)))
        ([#_"fn" f a b c d & s] (IFn'''applyTo f, (cons a (cons b (cons c (cons d (spread s)))))))
    )

    (defn complement [f]
        (fn
            ([] (not (f)))
            ([x] (not (f x)))
            ([x y] (not (f x y)))
            ([x y & s] (not (apply f x y s)))
        )
    )
)

(about #_"beagle.INamed"
    (defp INamed
        (#_"String" INamed'''getNamespace [#_"INamed" this])
        (#_"String" INamed'''getName [#_"INamed" this])
    )

    (-/extend-protocol INamed clojure.lang.Named
        (INamed'''getNamespace [this] (.getNamespace this))
        (INamed'''getName [this] (.getName this))
    )

    (defn named? [x] (satisfies? INamed x))

    (defn #_"String" namespace [#_"INamed" x] (INamed'''getNamespace x))

    (defn #_"String" name [x] (if (string? x) x (INamed'''getName #_"INamed" x)))
)

(about #_"beagle.IMeta"
    (defp IMeta
        (#_"meta" IMeta'''meta [#_"IMeta" this])
    )

    (-/extend-protocol IMeta clojure.lang.IMeta
        (IMeta'''meta [this] (.meta this))
    )

    (defn meta [x] (when (satisfies? IMeta x) (IMeta'''meta #_"IMeta" x)))
)

(about #_"beagle.IObj"
    (defp IObj
        (#_"IObj" IObj'''withMeta [#_"IObj" this, #_"meta" meta])
    )

    (-/extend-protocol IObj clojure.lang.IObj
        (IObj'''withMeta [this, meta] (.withMeta this, (-/into {} meta)))
    )

    (defn with-meta [#_"IObj" x m] (IObj'''withMeta x, m))

    (defn vary-meta [x f & args] (with-meta x (apply f (meta x) args)))
)

(about #_"beagle.IReference"
    (defp IReference
        (#_"meta" IReference'''alterMeta [#_"IReference" this, #_"fn" f, #_"seq" args])
        (#_"meta" IReference'''resetMeta [#_"IReference" this, #_"meta" m])
    )

    (-/extend-protocol IReference clojure.lang.IReference
        (IReference'''alterMeta [this, f, args] (.alterMeta this, f, args))
        (IReference'''resetMeta [this, m] (.resetMeta this, m))
    )

    (defn alter-meta! [#_"IReference" r f & args] (IReference'''alterMeta r, f, args))

    (defn reset-meta! [#_"IReference" r m] (IReference'''resetMeta r, m))
)

(about #_"beagle.IDeref"
    (defp IDeref
        (#_"Object" IDeref'''deref [#_"IDeref" this])
    )

    (-/extend-protocol IDeref clojure.lang.IDeref
        (IDeref'''deref [this] (.deref this))
    )

    (defn deref [#_"IDeref" ref] (IDeref'''deref ref))
)

(about #_"beagle.IAtom"
    (defp IAtom
        (#_"Object" IAtom'''swap [#_"IAtom" this, #_"fn" f, #_"seq" args])
        (#_"Object" IAtom'''reset [#_"IAtom" this, #_"Object" o'])
    )

    (-/extend-protocol IAtom clojure.lang.IAtom2
        (IAtom'''swap  [this, f, args] (.swap  this, f, args))
        (IAtom'''reset [this,    o']   (.reset this, o'))
    )
)

(about #_"beagle.Sequential"
    (defp Sequential)

    (-/extend-protocol Sequential clojure.lang.Sequential)

    (defn sequential? [x] (satisfies? Sequential x))
)

(about #_"beagle.Reversible"
    (defp Reversible
        (#_"seq" Reversible'''rseq [#_"Reversible" this])
    )

    (-/extend-protocol Reversible clojure.lang.Reversible
        (Reversible'''rseq [this] (.rseq this))
    )

    (defn reversible? [x] (satisfies? Reversible x))

    (defn rseq [#_"Reversible" s] (Reversible'''rseq s))
)

(about #_"beagle.Indexed"
    (defp Indexed
        (#_"Object" Indexed'''nth
            [#_"Indexed" this, #_"int" i]
            [#_"Indexed" this, #_"int" i, #_"value" not-found]
        )
    )

    (-/extend-protocol Indexed clojure.lang.Indexed
        (Indexed'''nth
            ([this, i] (.nth this, i))
            ([this, i, not-found] (.nth this, i, not-found))
        )
    )

    (defn indexed? [x] (satisfies? Indexed x))

    (defn nthnext [s n] (loop-when-recur [s (seq s) n n] (and s (pos? n)) [(next s) (dec n)] => s))
)

(about #_"beagle.ILookup"
    (defp ILookup
        (#_"Object" ILookup'''valAt
            [#_"ILookup" this, #_"key" key]
            [#_"ILookup" this, #_"key" key, #_"value" not-found]
        )
    )
)

(about #_"beagle.IPersistentCollection"
    (defp IPersistentCollection
        (#_"IPersistentCollection" IPersistentCollection'''conj [#_"IPersistentCollection" this, #_"Object" o])
        (#_"IPersistentCollection" IPersistentCollection'''empty [#_"IPersistentCollection" this])
    )

    (-/extend-protocol IPersistentCollection clojure.lang.IPersistentCollection
        (IPersistentCollection'''conj [this, o] (.cons this, o))
        (IPersistentCollection'''empty [this] (.empty this))
    )

    (defn coll? [x] (satisfies? IPersistentCollection x))

    (declare vector)
    (declare list)

    (defn conj
        ([] (vector))
        ([c] c)
        ([c x] (if (some? c) (IPersistentCollection'''conj c, x) (list x)))
        ([c x & s]
            (let [c (conj c x)]
                (recur-when s [c (first s) (next s)] => c)
            )
        )
    )

    (defn empty [coll]
        (when (coll? coll)
            (IPersistentCollection'''empty #_"IPersistentCollection" coll)
        )
    )

    (defn not-empty [coll] (when (seq coll) coll))
)

(about #_"beagle.IMapEntry"
    (defp IMapEntry
        (#_"Object" IMapEntry'''key [#_"IMapEntry" this])
        (#_"Object" IMapEntry'''val [#_"IMapEntry" this])
    )

    (-/extend-protocol IMapEntry clojure.lang.IMapEntry
        (IMapEntry'''key [this] (.key this))
        (IMapEntry'''val [this] (.val this))
    )

    (defn map-entry? [x] (satisfies? IMapEntry x))

    (defn key [#_"IMapEntry" e] (IMapEntry'''key e))
    (defn val [#_"IMapEntry" e] (IMapEntry'''val e))

    (declare map)

    (defn keys [m] (not-empty (map key m)))
    (defn vals [m] (not-empty (map val m)))
)

(about #_"beagle.Associative"
    (defp Associative
        (#_"Associative" Associative'''assoc [#_"Associative" this, #_"key" key, #_"value" val])
        (#_"boolean" Associative'''containsKey [#_"Associative" this, #_"key" key])
        (#_"IMapEntry" Associative'''entryAt [#_"Associative" this, #_"key" key])
    )

    (-/extend-protocol Associative clojure.lang.Associative
        (Associative'''assoc [this, key, val] (.assoc this, key, val))
        (Associative'''containsKey [this, key] (.containsKey this, key))
        (Associative'''entryAt [this, key] (.entryAt this, key))
    )

    (defn associative? [x] (satisfies? Associative x))

    (declare PersistentMap'new)

    (defn assoc
        ([#_"Associative" a k v]
            (if (some? a)
                (Associative'''assoc a, k, v)
                (PersistentMap'new (anew [ k, v ]))
            )
        )
        ([a k v & kvs]
            (let-when [a (assoc a k v)] kvs => a
                (when (next kvs) => (throw! "assoc expects even number of arguments after map/vector, found odd number")
                    (recur a (first kvs) (second kvs) (next (next kvs)))
                )
            )
        )
    )

    (declare get)

    (defn assoc-in [m [k & ks] v]
        (if ks
            (assoc m k (assoc-in (get m k) ks v))
            (assoc m k v)
        )
    )

    (defn update
        ([m k f] (assoc m k (f (get m k))))
        ([m k f x] (assoc m k (f (get m k) x)))
        ([m k f x y] (assoc m k (f (get m k) x y)))
        ([m k f x y & z] (assoc m k (apply f (get m k) x y z)))
    )

    (defn update-in [m ks f & args]
        (let [[k & ks] ks]
            (if ks
                (assoc m k (apply update-in (get m k) ks f args))
                (assoc m k (apply f (get m k) args))
            )
        )
    )
)

(about #_"beagle.IPersistentMap"
    (defp IPersistentMap
        (#_"IPersistentMap" IPersistentMap'''dissoc [#_"IPersistentMap" this, #_"key" key])
    )

    (-/extend-protocol IPersistentMap clojure.lang.IPersistentMap
        (IPersistentMap'''dissoc [this, key] (.without this, key))
    )

    (defn map? [x] (satisfies? IPersistentMap x))

    (defn dissoc
        ([m] m)
        ([#_"IPersistentMap" m k] (when (some? m) (IPersistentMap'''dissoc m, k)))
        ([m k & ks]
            (when-some [m (dissoc m k)]
                (recur-when ks [m (first ks) (next ks)] => m)
            )
        )
    )
)

(about #_"beagle.IPersistentSet"
    (defp IPersistentSet
        (#_"IPersistentSet" IPersistentSet'''disj [#_"IPersistentSet" this, #_"key" key])
        (#_"boolean" IPersistentSet'''contains? [#_"IPersistentSet" this, #_"key" key])
        (#_"Object" IPersistentSet'''get [#_"IPersistentSet" this, #_"key" key])
    )

    (-/extend-protocol IPersistentSet clojure.lang.IPersistentSet
        (IPersistentSet'''disj [this, key] (.disjoin this, key))
        (IPersistentSet'''contains? [this, key] (.contains this, key))
        (IPersistentSet'''get [this, key] (.get this, key))
    )

    (defn set? [x] (satisfies? IPersistentSet x))

    (defn disj
        ([s] s)
        ([#_"IPersistentSet" s k] (when (some? s) (IPersistentSet'''disj s, k)))
        ([s k & ks]
            (when-some [s (disj s k)]
                (recur-when ks [s (first ks) (next ks)] => s)
            )
        )
    )
)

(about #_"beagle.IPersistentStack"
    (defp IPersistentStack
        (#_"Object" IPersistentStack'''peek [#_"IPersistentStack" this])
        (#_"IPersistentStack" IPersistentStack'''pop [#_"IPersistentStack" this])
    )

    (-/extend-protocol IPersistentStack clojure.lang.IPersistentStack
        (IPersistentStack'''peek [this] (.peek this))
        (IPersistentStack'''pop [this] (.pop this))
    )

    (defn stack? [x] (satisfies? IPersistentStack x))

    (defn peek [s]
        (when (some? s)
            (IPersistentStack'''peek s)
        )
    )

    (defn butlast [s] (loop-when-recur [v (vector) s s] (next s) [(conj v (first s)) (next s)] => (seq v)))

    (defn pop [s]
        (when (some? s)
            (IPersistentStack'''pop s)
        )
    )
)

(about #_"beagle.IPersistentList"
    (defp IPersistentList)

    (-/extend-protocol IPersistentList clojure.lang.IPersistentList)

    (defn list? [x] (satisfies? IPersistentList x))
)

(about #_"beagle.IPersistentVector"
    (defp IPersistentVector
        (#_"IPersistentVector" IPersistentVector'''assocN [#_"IPersistentVector" this, #_"int" i, #_"value" val])
    )

    (-/extend-protocol IPersistentVector clojure.lang.IPersistentVector
        (IPersistentVector'''assocN [this, i, val] (.assocN this, i, val))
    )

    (defn vector? [x] (satisfies? IPersistentVector x))
)

(about #_"beagle.Atom"
    (defp Atom)
)

(about #_"beagle.AFn"
    #_abstract
    (defp AFn)
)

(about #_"beagle.Symbol"
    (defp Symbol)

    (-/extend-protocol Symbol clojure.lang.Symbol)

    (defn symbol? [x] (satisfies? Symbol x))
)

(about #_"beagle.Keyword"
    (defp Keyword)

    (-/extend-protocol Keyword clojure.lang.Keyword)

    (defn keyword? [x] (satisfies? Keyword x))
)

(about #_"beagle.Fn"
    #_abstract
    (defp Fn)

    (-/extend-protocol Fn clojure.lang.Fn)

    (defn fn? [x] (satisfies? Fn x))
)

(about #_"beagle.Closure"
    (defp Closure)
)

(about #_"beagle.ASeq"
    #_abstract
    (defp ASeq)
)

(about #_"beagle.LazySeq"
    (defp LazySeq)
)

(about #_"beagle.APersistentVector"
    (defp VSeq)
    (defp RSeq)
    #_abstract
    (defp APersistentVector)
)

(about #_"beagle.AMapEntry"
    #_abstract
    (defp AMapEntry)
)

(about #_"beagle.Cons"
    (defp Cons)
)

(about #_"beagle.MapEntry"
    (defp MapEntry)
)

(about #_"beagle.Namespace"
    (defp Namespace)
)

(about #_"beagle.PersistentMap"
    (defp MSeq)
    (defp PersistentMap)
)

(about #_"beagle.PersistentSet"
    (defp PersistentSet)
)

(about #_"beagle.PersistentList"
    (defp EmptyList)
    (defp PersistentList)
)

(about #_"beagle.PersistentVector"
    (defp VNode)
    (defp PersistentVector)
)

(about #_"beagle.Var"
    (defp Unbound)
    (defp Var)

    (-/extend-protocol Unbound clojure.lang.Var$Unbound)
    (-/extend-protocol Var clojure.lang.Var)

    (defn var? [v] (satisfies? Var v))
)

(about #_"defarray"
    (defn aget    [a i] (A'get a i))
    (defn alength [a]   (A'length a))

    (defn aclone [a]         (when (some? a) (A'clone a)))
    (defn acopy! [a i b j n] (System'arraycopy b, j, a, i, n) a)
    (defn aset!  [a i x]     (A'set a i x) a)
    (defn aswap! [a i f & s] (aset! a i (apply f (aget a i) s)))

    (defn anew [size-or-seq]
        (if (number? size-or-seq)
            (A'new (int! size-or-seq))
            (let [#_"seq" s (seq size-or-seq) #_"int" n (count s)]
                (loop-when-recur [#_"array" a (A'new n) #_"int" i 0 s s] (and (< i n) (some? s)) [(aset! a i (first s)) (inc i) (next s)] => a)
            )
        )
    )

    (defn qset!
        ([a k v]    (Mutable''mutate! a, k, v))
        ([a k v & kvs]
            (let [a (Mutable''mutate! a, k, v)]
                (recur-when kvs [a (first kvs) (second kvs) (next (next kvs))] => a)
            )
        )
    )

    (defn qswap!
        ([a k f]         (Mutable''mutate! a, k,       (f (ILookup''valAt a, k))))
        ([a k f x]       (Mutable''mutate! a, k,       (f (ILookup''valAt a, k) x)))
        ([a k f x y]     (Mutable''mutate! a, k,       (f (ILookup''valAt a, k) x y)))
        ([a k f x y & z] (Mutable''mutate! a, k, (apply f (ILookup''valAt a, k) x y z)))
    )
)

(about #_"append, str, pr, prn"
    (def #_"{char String}" char-name-string
        (-/hash-map
            \newline   "newline"
            \tab       "tab"
            \space     "space"
            \backspace "backspace"
            \formfeed  "formfeed"
            \return    "return"
        )
    )

    (defn #_"Appendable" append-chr [#_"Appendable" a, #_"char" x]
        (-> a (Appendable''append "\\") (Appendable''append (M'get char-name-string x x)))
    )

    (def #_"{char String}" char-escape-string
        (-/hash-map
            \newline   "\\n"
            \tab       "\\t"
            \return    "\\r"
            \"         "\\\""
            \\         "\\\\"
            \formfeed  "\\f"
            \backspace "\\b"
        )
    )

    (defn #_"Appendable" append-str [#_"Appendable" a, #_"String" x]
        (let [
            a (Appendable''append a, "\"")
            a (-/reduce #(Appendable''append %1, (M'get char-escape-string %2 %2)) a x)
            a (Appendable''append a, "\"")
        ]
            a
        )
    )

    (defn #_"Appendable" append-rex [#_"Appendable" a, #_"Pattern" x]
        (let [
            a (Appendable''append a, "#\"")
            a
                (loop-when [a a [#_"char" c & #_"seq" r :as #_"seq" s] (seq (Pattern''pattern x)) q? false] (some? s) => a
                    (case! c
                        \\  (let [[c & r] r] (recur (-> a (Appendable''append "\\") (Appendable''append c)) r (if q? (not= c \E) (= c \Q))))
                        \"                   (recur (-> a (Appendable''append (if q? "\\E\\\"\\Q" "\\\""))) r q?)
                                             (recur (-> a (Appendable''append c))                           r q?)
                    )
                )
            a (Appendable''append a, "\"")
        ]
            a
        )
    )

    (defp SeqForm)
    (defp VecForm)
    (defp MapForm)
    (defp SetForm)

    (defn #_"Appendable" append* [#_"Appendable" a, #_"String" b, #_"fn" f'append, #_"String" c, #_"String" d, #_"Seqable" q]
        (let [a (let-when [a (Appendable''append a, b) #_"seq" s (seq q)] (some? s) => a
                    (loop [a a s s]
                        (let-when [a (f'append a (first s)) s (next s)] (some? s) => a
                            (recur (Appendable''append a, c) s)
                        )
                    )
                )]
            (Appendable''append a, d)
        )
    )

    (declare append)

    (defn #_"Appendable" append-seq [#_"Appendable" a, #_"seq" x]    (append* a "(" append " " ")" x))
    (defn #_"Appendable" append-vec [#_"Appendable" a, #_"vector" x] (append* a "[" append " " "]" x))
    (defn #_"Appendable" append-map [#_"Appendable" a, #_"map" x]    (append* a "{" (fn [a e] (-> a (append (key e)) (Appendable''append " ") (append (val e)))) ", " "}" x))
    (defn #_"Appendable" append-set [#_"Appendable" a, #_"set" x]    (append* a "#{" append " " "}" x))

    (defn #_"Appendable" append [#_"Appendable" a, #_"any" x]
        (case! x
            nil   (Appendable''append a, "nil")
            false (Appendable''append a, "false")
            true  (Appendable''append a, "true")
            (cond
                (number? x) (Appendable''append a, (Number''toString x))
                (string? x) (append-str a x)
                :else
                (condp satisfies? x
                    IAppend (IAppend'''append x, a)
                    SeqForm (append-seq a x)
                    VecForm (append-vec a x)
                    MapForm (append-map a x)
                    SetForm (append-set a x)
                    (cond
                        (seq? x)     (append-seq a x)
                        (vector? x)  (append-vec a x)
                        (map? x)     (append-map a x)
                        (set? x)     (append-set a x)
                        (char? x)    (append-chr a x)
                        (pattern? x) (append-rex a x)
                        :else        (Appendable''append a, (Object''toString x))
                    )
                )
            )
        )
    )

    (defn #_"Appendable" append! [#_"Appendable" a, #_"any" x]
        (if (or (string? x) (char? x)) (Appendable''append a, x) (append a x))
    )

    (defn #_"String" str
        ([] "")
        ([x] (if (some? x) (-> (StringBuilder'new) (append! x) (StringBuilder''toString)) ""))
        ([x & s]
            ((fn [#_"StringBuilder" sb s] (recur-when s [(append! sb (first s)) (next s)] => (StringBuilder''toString sb)))
                (-> (StringBuilder'new) (append! x)) s
            )
        )
    )

    (defn space   [] (Appendable''append -/*out* \space)   nil)
    (defn newline [] (Appendable''append -/*out* \newline) nil)
    (defn flush   [] (Flushable''flush   -/*out*)          nil)

    (defn pr
        ([] nil)
        ([x] (append -/*out* x) nil)
        ([x & s]
            (pr x) (space)
            (let-when [[x & s] s] (some? s) => (pr x)
                (recur x s)
            )
        )
    )

    (defn print
        ([] nil)
        ([x] (append! -/*out* x) nil)
        ([x & s]
            (print x) (space)
            (let-when [[x & s] s] (some? s) => (print x)
                (recur x s)
            )
        )
    )

    (defn prn     [& s] (apply pr    s) (newline) (flush) nil)
    (defn println [& s] (apply print s) (newline) (flush) nil)
)

(about #_"beagle.Atom"

(about #_"Atom"
    (declare Atom''deref)

    (defq Atom [#_"AtomicReference" meta, #_"AtomicReference" data]
        java.util.concurrent.Future (get [_] (Atom''deref _))
    )

    (defn #_"Atom" Atom'new
        ([#_"Object" data] (Atom'new nil, data))
        ([#_"meta" meta, #_"Object" data]
            (new* Atom'class (anew [(AtomicReference'new meta), (AtomicReference'new data)]))
        )
    )

    (defn #_"meta" Atom''meta [#_"Atom" this]
        (AtomicReference''get (:meta this))
    )

    (defn #_"meta" Atom''alterMeta [#_"Atom" this, #_"fn" f, #_"seq" args]
        (loop []
            (let [#_"meta" m (AtomicReference''get (:meta this)) #_"meta" m' (apply f m args)]
                (when (AtomicReference''compareAndSet (:meta this), m, m') => (recur)
                    m'
                )
            )
        )
    )

    (defn #_"meta" Atom''resetMeta [#_"Atom" this, #_"meta" m']
        (AtomicReference''set (:meta this), m')
        m'
    )

    (defn #_"Object" Atom''deref [#_"Atom" this]
        (AtomicReference''get (:data this))
    )

    (defn #_"Object" Atom''swap [#_"Atom" this, #_"fn" f, #_"seq" args]
        (loop []
            (let [#_"Object" o (AtomicReference''get (:data this)) #_"Object" o' (apply f o args)]
                (when (AtomicReference''compareAndSet (:data this), o, o') => (recur)
                    o'
                )
            )
        )
    )

    (defn #_"Object" Atom''reset [#_"Atom" this, #_"Object" o']
        (AtomicReference''set (:data this), o')
        o'
    )

    (defm Atom IMeta
        (IMeta'''meta => Atom''meta)
    )

    (defm Atom IReference
        (IReference'''alterMeta => Atom''alterMeta)
        (IReference'''resetMeta => Atom''resetMeta)
    )

    (defm Atom IDeref
        (IDeref'''deref => Atom''deref)
    )

    (defm Atom IAtom
        (IAtom'''swap => Atom''swap)
        (IAtom'''reset => Atom''reset)
    )
)

(defn atom
    ([x] (Atom'new x))
    ([m x] (Atom'new m x))
)

(defn swap! [#_"IAtom" a f & args] (IAtom'''swap a, f, args))

(defn reset! [#_"IAtom" a x'] (IAtom'''reset a, x'))
)

(about #_"beagle.Reduce"

(defn reduce
    ([f s] (if-some [s (seq s)] (reduce f (first s) (next s)) (f)))
    ([f r s] (if-some [s (seq s)] (recur f (f r (first s)) (next s)) r))
)

(defn into [to from] (reduce conj to from))

(defn mapv
    ([f coll] (reduce #(conj %1 (f %2)) (vector) coll))
    ([f c1 c2] (into (vector) (map f c1 c2)))
    ([f c1 c2 c3] (into (vector) (map f c1 c2 c3)))
    ([f c1 c2 c3 & colls] (into (vector) (apply map f c1 c2 c3 colls)))
)
)

(about #_"beagle.Util"

(about #_"Util"
    (declare Symbol''equals)
    (declare Keyword''equals)

    (defn #_"boolean" Util'equiv [#_"Object" a, #_"Object" b]
        (cond
            (identical? a b)              true
            (nil? a)                      false
            (and (number? a) (number? b)) (-/== a b)
            (coll? a)                     (IObject'''equals a, b)
            (coll? b)                     (IObject'''equals b, a)
            (-/instance? (:on-interface Symbol) a)  (Symbol''equals a, b)
            (-/instance? (:on-interface Symbol) b)  (Symbol''equals b, a)
            (-/instance? (:on-interface Keyword) a) (Keyword''equals a, b)
            (-/instance? (:on-interface Keyword) b) (Keyword''equals b, a)
            :else                         (IObject'''equals a, b)
        )
    )
)

#_oops!
(defn =
    ([x] true)
    ([x y] (Util'equiv x y))
    ([x y & s] (and (= x y) (recur-when (next s) [y (first s) (next s)] => (= y (first s)))))
)

(defn not=
    ([x] false)
    ([x y] (not (= x y)))
    ([x y & s] (not (apply = x y s)))
)
)

(about #_"beagle.Numbers"

(defn max
    ([x] x)
    ([x y] (if (> x y) x y))
    ([x y & s] (reduce max (max x y) s))
)

(defn min
    ([x] x)
    ([x y] (if (< x y) x y))
    ([x y & s] (reduce min (min x y) s))
)

(defn even? [n]
    (when (int? n) => (throw! (str "argument must be an integer: " n))
        (zero? (& n 1))
    )
)

(defn odd? [n] (not (even? n)))
)

(about #_"beagle.AFn"

(about #_"AFn"
    (defn #_"void" AFn'throwArity [#_"fn" f, #_"int" n]
        (throw! (str "wrong number of args (" (if (neg? n) (str "more than " (dec (- n))) n) ") passed to " f))
    )

    (defn #_"Object" AFn'applyTo [#_"fn" f, #_"seq" s]
        (case! (count s (inc 9))
            0                                           (IFn'''invoke f)
            1 (let [[a1] s]                             (IFn'''invoke f, a1))
            2 (let [[a1 a2] s]                          (IFn'''invoke f, a1, a2))
            3 (let [[a1 a2 a3] s]                       (IFn'''invoke f, a1, a2, a3))
            4 (let [[a1 a2 a3 a4] s]                    (IFn'''invoke f, a1, a2, a3, a4))
            5 (let [[a1 a2 a3 a4 a5] s]                 (IFn'''invoke f, a1, a2, a3, a4, a5))
            6 (let [[a1 a2 a3 a4 a5 a6] s]              (IFn'''invoke f, a1, a2, a3, a4, a5, a6))
            7 (let [[a1 a2 a3 a4 a5 a6 a7] s]           (IFn'''invoke f, a1, a2, a3, a4, a5, a6, a7))
            8 (let [[a1 a2 a3 a4 a5 a6 a7 a8] s]        (IFn'''invoke f, a1, a2, a3, a4, a5, a6, a7, a8))
            9 (let [[a1 a2 a3 a4 a5 a6 a7 a8 a9] s]     (IFn'''invoke f, a1, a2, a3, a4, a5, a6, a7, a8, a9))
              (let [[a1 a2 a3 a4 a5 a6 a7 a8 a9 & s] s] (IFn'''invoke f, a1, a2, a3, a4, a5, a6, a7, a8, a9, s))
        )
    )
)
)

(about #_"beagle.Symbol"

(about #_"Symbol"
    (declare Symbol''withMeta Symbol''equals)

    (defq Symbol [#_"meta" _meta, #_"String" ns, #_"String" name]
        clojure.lang.IMeta (meta [_] (-/into {} (:_meta _)))
        clojure.lang.IObj (withMeta [_, m] (Symbol''withMeta _, m))
        clojure.lang.Named (getNamespace [_] (:ns _)) (getName [_] (:name _))
        java.lang.Object (equals [_, o] (Symbol''equals _, o)) (toString [_] (str _))
    )

    #_inherit
    (defm Symbol AFn)

    (defn #_"Symbol" Symbol'new
        ([#_"String" ns, #_"String" name] (Symbol'new nil, ns, name))
        ([#_"meta" meta, #_"String" ns, #_"String" name]
            (new* Symbol'class (anew [meta, ns, name]))
        )
    )

    (defn #_"Symbol" Symbol''withMeta [#_"Symbol" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (Symbol'new meta, (:ns this), (:name this))
        )
    )

    (defn #_"Symbol" Symbol'intern
        ([#_"String" nsname]
            (let [#_"int" i (String''indexOf nsname, (int \/))]
                (if (or (= i -1) (= nsname "/"))
                    (Symbol'new nil, nsname)
                    (Symbol'new (String''substring nsname, 0, i), (String''substring nsname, (inc i)))
                )
            )
        )
        ([#_"String" ns, #_"String" name]
            (Symbol'new ns, name)
        )
    )

    (defn #_"boolean" Symbol''equals [#_"Symbol" this, #_"Object" that]
        (or (identical? this that)
            (and (symbol? that) (= (:ns this) (#_:ns namespace that)) (= (:name this) (#_:name name that)))
        )
    )

    (defn #_"Appendable" Symbol''append [#_"Symbol" this, #_"Appendable" a]
        (if (some? (:ns this)) (-> a (Appendable''append (:ns this)) (Appendable''append "/") (Appendable''append (:name this))) (Appendable''append a, (:name this)))
    )

    (defn #_"Object" Symbol''invoke
        ([#_"Symbol" this, #_"Object" obj] (get obj this))
        ([#_"Symbol" this, #_"Object" obj, #_"value" not-found] (get obj this not-found))
    )

    (defm Symbol IMeta
        (IMeta'''meta => :_meta)
    )

    (defm Symbol IObj
        (IObj'''withMeta => Symbol''withMeta)
    )

    (defm Symbol INamed
        (INamed'''getNamespace => :ns)
        (INamed'''getName => :name)
    )

    (defm Symbol IObject
        (IObject'''equals => Symbol''equals)
    )

    (defm Symbol IAppend
        (IAppend'''append => Symbol''append)
    )

    (defm Symbol IFn
        (IFn'''invoke => Symbol''invoke)
        (IFn'''applyTo => AFn'applyTo)
    )
)

(defn symbol
    ([name] (if (symbol? name) name (Symbol'intern name)))
    ([ns name] (Symbol'intern ns, name))
)

(defn symbol! [s] (symbol (if (clojure-symbol? s) (str s) s)))

(-/defmethod -/print-method (:on-interface Symbol) [o w] (.write w, (str o)))
)

(about #_"beagle.Keyword"

(about #_"Keyword"
    (declare Keyword''equals Keyword''invoke)

    (defq Keyword [#_"Symbol" sym]
        clojure.lang.Named (getNamespace [_] (:ns (:sym _))) (getName [_] (:name (:sym _)))
        java.lang.Object (equals [_, o] (Keyword''equals _, o)) (toString [_] (str _))
        clojure.lang.IFn (invoke [_, a] (Keyword''invoke _, a))
    )

    #_inherit
    (defm Keyword AFn)

    (defn #_"Keyword" Keyword'new [#_"Symbol" sym]
        (new* Keyword'class (anew [sym]))
    )

    (defn #_"Keyword" Keyword'intern [#_"Symbol" sym]
        (let [sym
                (when (some? (meta sym)) => sym
                    (with-meta sym nil)
                )]
            (Keyword'new sym)
        )
    )

    (defn #_"String" Keyword''getNamespace [#_"Keyword" this]
        (INamed'''getNamespace (:sym this))
    )

    (defn #_"String" Keyword''getName [#_"Keyword" this]
        (INamed'''getName (:sym this))
    )

    (defn #_"boolean" Keyword''equals [#_"Keyword" this, #_"Object" that]
        (or (identical? this that)
            (and (clojure-keyword? that) (Symbol''equals (:sym this), (Keyword''sym that)))
            (and (keyword? that) (Symbol''equals (:sym this), (:sym that)))
        )
    )

    (defn #_"Appendable" Keyword''append [#_"Keyword" this, #_"Appendable" a]
        (-> a (Appendable''append ":") (append (:sym this)))
    )

    (defn #_"Object" Keyword''invoke
        ([#_"Keyword" this, #_"Object" obj] (get obj this))
        ([#_"Keyword" this, #_"Object" obj, #_"value" not-found] (get obj this not-found))
    )

    (defm Keyword INamed
        (INamed'''getNamespace => Keyword''getNamespace)
        (INamed'''getName => Keyword''getName)
    )

    (defm Keyword IObject
        (IObject'''equals => Keyword''equals)
    )

    (defm Keyword IAppend
        (IAppend'''append => Keyword''append)
    )

    (defm Keyword IFn
        (IFn'''invoke => Keyword''invoke)
        (IFn'''applyTo => AFn'applyTo)
    )
)

(defn keyword
    ([name]
        (cond
            (keyword? name) name
            (symbol? name) (Keyword'intern #_"Symbol" name)
            (string? name) (Keyword'intern (symbol #_"String" name))
        )
    )
    ([ns name] (Keyword'intern (symbol ns name)))
)

(defn keyword! [k] (keyword (if (clojure-keyword? k) (name k) k)))

(-/defmethod -/print-method (:on-interface Keyword) [o w] (.write w, (str o)))
)

(about #_"beagle.Fn"

(about #_"Fn"
    (defq Fn [])

    #_inherit
    (defm Fn AFn)

    (defn #_"Fn" Fn'new []
        (new* Fn'class (anew []))
    )

    (defn #_"Object" Fn''invoke
        ([#_"Fn" this]                                                   (AFn'throwArity this,   0))
        ([#_"Fn" this, a1]                                               (AFn'throwArity this,   1))
        ([#_"Fn" this, a1, a2]                                           (AFn'throwArity this,   2))
        ([#_"Fn" this, a1, a2, a3]                                       (AFn'throwArity this,   3))
        ([#_"Fn" this, a1, a2, a3, a4]                                   (AFn'throwArity this,   4))
        ([#_"Fn" this, a1, a2, a3, a4, a5]                               (AFn'throwArity this,   5))
        ([#_"Fn" this, a1, a2, a3, a4, a5, a6]                           (AFn'throwArity this,   6))
        ([#_"Fn" this, a1, a2, a3, a4, a5, a6, a7]                       (AFn'throwArity this,   7))
        ([#_"Fn" this, a1, a2, a3, a4, a5, a6, a7, a8]                   (AFn'throwArity this,   8))
        ([#_"Fn" this, a1, a2, a3, a4, a5, a6, a7, a8, a9]               (AFn'throwArity this,   9))
        ([#_"Fn" this, a1, a2, a3, a4, a5, a6, a7, a8, a9, #_"seq" args] (AFn'throwArity this, -10))
    )

    (defm Fn IFn
        (IFn'''invoke => Fn''invoke)
        (IFn'''applyTo => AFn'applyTo)
    )
)
)

(about #_"beagle.Closure"

(about #_"Closure"
    (declare Closure''invoke Closure''applyTo)

    (defq Closure [#_"meta" _meta, #_"FnExpr" fun, #_"map'" _env]
        clojure.lang.IFn (invoke [_] (Closure''invoke _)) (invoke [_, a1] (Closure''invoke _, a1)) (invoke [_, a1, a2] (Closure''invoke _, a1, a2)) (applyTo [_, args] (Closure''applyTo _, args))
    )

    #_inherit
    (defm Closure Fn AFn)

    (defn #_"Closure" Closure'new
        ([#_"FnExpr" fun, #_"map" env] (Closure'new nil, fun, env))
        ([#_"meta" meta, #_"FnExpr" fun, #_"map" env]
            (new* Closure'class (anew [meta, fun, (atom env)]))
        )
    )

    (defn #_"Closure" Closure''withMeta [#_"Closure" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (new* Closure'class (anew [meta, (:fun this), (:_env this)]))
        )
    )

    (defn #_"Object" Closure''invoke
        ([#_"Closure" this]                                                 (IFn'''applyTo this, nil))
        ([#_"Closure" this, a1]                                             (IFn'''applyTo this, (list a1)))
        ([#_"Closure" this, a1, a2]                                         (IFn'''applyTo this, (list a1 a2)))
        ([#_"Closure" this, a1, a2, a3]                                     (IFn'''applyTo this, (list a1 a2 a3)))
        ([#_"Closure" this, a1, a2, a3, a4]                                 (IFn'''applyTo this, (list a1 a2 a3 a4)))
        ([#_"Closure" this, a1, a2, a3, a4, a5]                             (IFn'''applyTo this, (list a1 a2 a3 a4 a5)))
        ([#_"Closure" this, a1, a2, a3, a4, a5, a6]                         (IFn'''applyTo this, (list a1 a2 a3 a4 a5 a6)))
        ([#_"Closure" this, a1, a2, a3, a4, a5, a6, a7]                     (IFn'''applyTo this, (list a1 a2 a3 a4 a5 a6 a7)))
        ([#_"Closure" this, a1, a2, a3, a4, a5, a6, a7, a8]                 (IFn'''applyTo this, (list a1 a2 a3 a4 a5 a6 a7 a8)))
        ([#_"Closure" this, a1, a2, a3, a4, a5, a6, a7, a8, a9]             (IFn'''applyTo this, (list a1 a2 a3 a4 a5 a6 a7 a8 a9)))
        ([#_"Closure" this, a1, a2, a3, a4, a5, a6, a7, a8, a9, #_"seq" a*] (IFn'''applyTo this, (list* a1 a2 a3 a4 a5 a6 a7 a8 a9 a*)))
    )

    (declare Compiler'MAX_POSITIONAL_ARITY)
    (declare Machine'compute)
    (declare compile-and-memoize)

    (defn #_"Object" Closure''applyTo [#_"Closure" this, #_"seq" args]
        (let [
            #_"FnMethod" fm
                (let [#_"int" m (inc Compiler'MAX_POSITIONAL_ARITY) #_"int" n (min (count args m) m)]
                    (or (get (:regulars (:fun this)) n)
                        (let-when [fm (:variadic (:fun this))] (and (some? fm) (<= (dec (- (:arity fm))) n)) => (AFn'throwArity this, (if (< n m) n (- m)))
                            fm
                        )
                    )
                )
            #_"array" vars
                (let [
                    #_"int" m (inc (reduce max (inc -1) (map :idx (vals @(:'locals fm)))))
                    #_"int" n (:arity fm) n (if (neg? n) (- n) (inc n))
                ]
                    (loop-when-recur [vars (-> (anew m) (aset! 0 this)) #_"int" i 1 #_"seq" s (seq args)]
                                     (< i n)
                                     [(aset! vars i (first s)) (inc i) (next s)]
                                  => (if (some? s) (aset! vars i s) vars)
                    )
                )
        ]
            (Machine'compute (compile-and-memoize fm), vars)
        )
    )

    (defm Closure IMeta
        (IMeta'''meta => :_meta)
    )

    (defm Closure IObj
        (IObj'''withMeta => Closure''withMeta)
    )

    (defm Closure IFn
        (IFn'''invoke => Closure''invoke)
        (IFn'''applyTo => Closure''applyTo)
    )
)
)

(about #_"beagle.ASeq"

(about #_"ASeq"
    (defn #_"boolean" ASeq''equals [#_"ASeq" this, #_"Object" that]
        (or (identical? this that)
            (and (sequential? that)
                (loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    )
)
)

(about #_"beagle.Cons"

(about #_"Cons"
    (declare Cons''withMeta Cons''seq Cons''next Cons''count)
    (declare cons)

    (defq Cons [#_"meta" _meta, #_"Object" car, #_"seq" cdr] SeqForm
        clojure.lang.IMeta (meta [_] (-/into {} (:_meta _)))
        clojure.lang.IObj (withMeta [_, m] (Cons''withMeta _, m))
        clojure.lang.ISeq (seq [_] (Cons''seq _)) (first [_] (:car _)) (next [_] (Cons''next _)) (more [_] (or (Cons''next _) ()))
        clojure.lang.IPersistentCollection (cons [_, o] (cons o _)) (count [_] (Cons''count _)) (equiv [_, o] (ASeq''equals _, o))
        clojure.lang.Sequential
    )

    #_inherit
    (defm Cons ASeq)

    (defn #_"Cons" Cons'new
        ([#_"Object" car, #_"seq" cdr] (Cons'new nil, car, cdr))
        ([#_"meta" meta, #_"Object" car, #_"seq" cdr]
            (new* Cons'class (anew [meta, car, cdr]))
        )
    )

    (defn #_"Cons" Cons''withMeta [#_"Cons" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (Cons'new meta, (:car this), (:cdr this))
        )
    )

    (defn #_"seq" Cons''seq [#_"Cons" this]
        this
    )

    (defn #_"seq" Cons''next [#_"Cons" this]
        (seq (:cdr this))
    )

    (defn #_"int" Cons''count [#_"Cons" this]
        (inc (count (:cdr this)))
    )

    (defm Cons IMeta
        (IMeta'''meta => :_meta)
    )

    (defm Cons IObj
        (IObj'''withMeta => Cons''withMeta)
    )

    (defm Cons Sequential)

    (defm Cons Seqable
        (Seqable'''seq => Cons''seq)
    )

    (defm Cons ISeq
        (ISeq'''first => :car)
        (ISeq'''next => Cons''next)
    )

    (defm Cons Counted
        (Counted'''count => Cons''count)
    )

    (defm Cons IObject
        (IObject'''equals => ASeq''equals)
    )
)

(defn cons [x s] (Cons'new x, (seq s)))
)

(about #_"beagle.LazySeq"

(about #_"LazySeq"
    (declare LazySeq''conj LazySeq''seq LazySeq''first LazySeq''next)

    (defq LazySeq [#_"meta" _meta, #_"fn'" f, #_"Object'" o, #_"seq'" s] SeqForm
        clojure.lang.IPersistentCollection (cons [_, o] (LazySeq''conj _, o))
        clojure.lang.ISeq (seq [_] (LazySeq''seq _)) (first [_] (LazySeq''first _)) (next [_] (LazySeq''next _)) (more [_] (or (LazySeq''next _) ()))
        clojure.lang.Sequential
    )

    (defn #_"LazySeq" LazySeq'init [#_"meta" meta, #_"fn" f, #_"seq" s]
        (new* LazySeq'class (anew [meta, (atom f), (atom nil), (atom s)]))
    )

    (defn #_"LazySeq" LazySeq'new
        ([#_"fn" f]                 (LazySeq'init nil,  f,   nil))
        ([#_"meta" meta, #_"seq" s] (LazySeq'init meta, nil, s  ))
    )

    (defn #_"LazySeq" LazySeq''withMeta [#_"LazySeq" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (LazySeq'new meta, (seq this))
        )
    )

    (defn #_"cons" LazySeq''conj [#_"LazySeq" this, #_"Object" o]
        (cons o this)
    )

    (defn #_"IPersistentCollection" LazySeq''empty [#_"LazySeq" this]
        (list)
    )

    (defn #_"seq" LazySeq''seq [#_"LazySeq" this]
        (do #_"locking this"
            (letfn [(step- [this]
                        (when-some [#_"fn" f @(:f this)]
                            (reset! (:f this) nil)
                            (reset! (:o this) (f))
                        )
                        (or @(:o this) @(:s this))
                    )]
                (step- this)
                (when-some [#_"Object" o @(:o this)]
                    (reset! (:o this) nil)
                    (reset! (:s this) (loop-when-recur o (satisfies? LazySeq o) (step- o) => (seq o)))
                )
                @(:s this)
            )
        )
    )

    (defn #_"Object" LazySeq''first [#_"LazySeq" this]
        (when-some [#_"seq" s (seq this)]
            (first s)
        )
    )

    (defn #_"seq" LazySeq''next [#_"LazySeq" this]
        (when-some [#_"seq" s (seq this)]
            (next s)
        )
    )

    (defn #_"boolean" LazySeq''equals [#_"LazySeq" this, #_"Object" that]
        (if-some [#_"seq" s (seq this)]
            (= s that)
            (and (sequential? that) (nil? (seq that)))
        )
    )

    (defm LazySeq IMeta
        (IMeta'''meta => :_meta)
    )

    (defm LazySeq IObj
        (IObj'''withMeta => LazySeq''withMeta)
    )

    (defm LazySeq IPersistentCollection
        (IPersistentCollection'''conj => LazySeq''conj)
        (IPersistentCollection'''empty => LazySeq''empty)
    )

    (defm LazySeq Sequential)

    (defm LazySeq Seqable
        (Seqable'''seq => LazySeq''seq)
    )

    (defm LazySeq ISeq
        (ISeq'''first => LazySeq''first)
        (ISeq'''next => LazySeq''next)
    )

    (defm LazySeq IObject
        (IObject'''equals => LazySeq''equals)
    )
)

(defmacro lazy-seq [& body] `(LazySeq'new (fn* [] ~@body)))

(defn dorun
    ([s]
        (when-some [s (seq s)]
            (recur (next s))
        )
    )
    ([n s]
        (when (pos? n)
            (when-some [s (seq s)]
                (recur (dec n) (next s))
            )
        )
    )
)

(defn doall
    ([s] (dorun s) s)
    ([n s] (dorun n s) s)
)

(defn concat
    ([] (lazy-seq nil))
    ([x] (lazy-seq x))
    ([x y]
        (lazy-seq
            (let-when [s (seq x)] s => y
                (cons (first s) (concat (next s) y))
            )
        )
    )
    ([x y & z]
        (letfn [(cat- [s z]
                    (lazy-seq
                        (let [s (seq s)]
                            (cond
                                s (cons (first s) (cat- (next s) z))
                                z (cat- (first z) (next z))
                            )
                        )
                    )
                )]
            (cat- (concat x y) z)
        )
    )
)

(defn comp
    ([] identity)
    ([f] f)
    ([f g]
        (fn
            ([] (f (g)))
            ([x] (f (g x)))
            ([x y] (f (g x y)))
            ([x y & z] (f (apply g x y z)))
        )
    )
    ([f g & fs] (reduce comp (list* f g fs)))
)

(defn partial
    ([f] f)
    ([f a]
        (fn
            ([] (f a))
            ([x] (f a x))
            ([x y] (f a x y))
            ([x y z] (f a x y z))
            ([x y z & args] (apply f a x y z args))
        )
    )
    ([f a b]
        (fn
            ([] (f a b))
            ([x] (f a b x))
            ([x y] (f a b x y))
            ([x y z] (f a b x y z))
            ([x y z & args] (apply f a b x y z args))
        )
    )
    ([f a b c]
        (fn
            ([] (f a b c))
            ([x] (f a b c x))
            ([x y] (f a b c x y))
            ([x y z] (f a b c x y z))
            ([x y z & args] (apply f a b c x y z args))
        )
    )
    ([f a b c & more]
        (fn [& args] (apply f a b c (concat more args)))
    )
)

(defn every? [f? s]
    (cond
        (nil? (seq s)) true
        (f? (first s)) (recur f? (next s))
        :else false
    )
)

(defn some [f? s]
    (when (seq s)
        (or (f? (first s)) (recur f? (next s)))
    )
)

(defn map
    ([f s]
        (lazy-seq
            (when-some [s (seq s)]
                (cons (f (first s)) (map f (next s)))
            )
        )
    )
    ([f s1 s2]
        (lazy-seq
            (let-when [s1 (seq s1) s2 (seq s2)] (and s1 s2)
                (cons (f (first s1) (first s2)) (map f (next s1) (next s2)))
            )
        )
    )
    ([f s1 s2 s3]
        (lazy-seq
            (let-when [s1 (seq s1) s2 (seq s2) s3 (seq s3)] (and s1 s2 s3)
                (cons (f (first s1) (first s2) (first s3)) (map f (next s1) (next s2) (next s3)))
            )
        )
    )
    ([f s1 s2 s3 & z]
        (letfn [(map- [s]
                    (lazy-seq
                        (let-when [s (map seq s)] (every? identity s)
                            (cons (map first s) (map- (map next s)))
                        )
                    )
                )]
            (map #(apply f %) (map- (conj z s3 s2 s1)))
        )
    )
)

(defn map-indexed [f s]
    (letfn [(mapi- [i s]
                (lazy-seq
                    (when-some [s (seq s)]
                        (cons (f i (first s)) (mapi- (inc i) (next s)))
                    )
                )
            )]
        (mapi- 0 s)
    )
)

(defn mapcat [f & s] (apply concat (apply map f s)))

(defmacro lazy-cat [& s]
    `(concat ~@(map #(list `lazy-seq %) s))
)

(defn filter [f? s]
    (lazy-seq
        (when-some [s (seq s)]
            (let-when [x (first s)] (f? x) => (filter f? (next s))
                (cons x (filter f? (next s)))
            )
        )
    )
)

(defn remove [f? s] (filter (complement f?) s))

(defn take [n s]
    (lazy-seq
        (when (pos? n)
            (when-some [s (seq s)]
                (cons (first s) (take (dec n) (next s)))
            )
        )
    )
)

(defn take-while [f? s]
    (lazy-seq
        (when-some [s (seq s)]
            (let-when [x (first s)] (f? x)
                (cons x (take-while f? (next s)))
            )
        )
    )
)

(defn drop [n s]
    (letfn [(drop- [n s]
                (let [s (seq s)]
                    (recur-when (and (pos? n) s) [(dec n) (next s)] => s)
                )
            )]
        (lazy-seq (drop- n s))
    )
)

(defn drop-while [f? s]
    (letfn [(drop- [f? s]
                (let [s (seq s)]
                    (recur-when (and s (f? (first s))) [f? (next s)] => s)
                )
            )]
        (lazy-seq (drop- f? s))
    )
)

(defn split-at [n s] [(take n s) (drop n s)])

(defn split-with [f? s] [(take-while f? s) (drop-while f? s)])

(defn take-nth [n s]
    (lazy-seq
        (when-some [s (seq s)]
            (cons (first s) (take-nth n (drop n s)))
        )
    )
)

(defn interleave
    ([] (list))
    ([c1] (lazy-seq c1))
    ([c1 c2]
        (lazy-seq
            (let-when [s1 (seq c1) s2 (seq c2)] (and s1 s2)
                (cons (first s1) (cons (first s2) (interleave (next s1) (next s2))))
            )
        )
    )
    ([c1 c2 & cs]
        (lazy-seq
            (let-when [ss (map seq (conj cs c2 c1))] (every? identity ss)
                (concat (map first ss) (apply interleave (map next ss)))
            )
        )
    )
)

(defn partition
    ([n s] (partition n n s))
    ([n step s]
        (lazy-seq
            (when-some [s (seq s)]
                (let-when [p (take n s)] (= (count p) n)
                    (cons p (partition n step (nthnext s step)))
                )
            )
        )
    )
    ([n step pad s]
        (lazy-seq
            (when-some [s (seq s)]
                (let-when [p (take n s)] (= (count p) n) => (list (take n (concat p pad)))
                    (cons p (partition n step pad (nthnext s step)))
                )
            )
        )
    )
)

(defn partition-all
    ([n s] (partition-all n n s))
    ([n step s]
        (lazy-seq
            (when-some [s (seq s)]
                (let [p (doall (take n s))]
                    (cons p (partition-all n step (nthnext s step)))
                )
            )
        )
    )
)
)

(about #_"beagle.APersistentVector"

(about #_"VSeq"
    (declare VSeq''seq VSeq''first VSeq''next)

    (defq VSeq [#_"meta" _meta, #_"vector" v, #_"int" i] SeqForm
        clojure.lang.ISeq (seq [_] (VSeq''seq _)) (first [_] (VSeq''first _)) (next [_] (VSeq''next _)) (more [_] (or (VSeq''next _) ()))
        clojure.lang.Sequential
    )

    #_inherit
    (defm VSeq ASeq)

    (defn #_"VSeq" VSeq'new
        ([#_"vector" v, #_"int" i] (VSeq'new nil, v, i))
        ([#_"meta" meta, #_"vector" v, #_"int" i]
            (new* VSeq'class (anew [meta, v, i]))
        )
    )

    (defn #_"VSeq" VSeq''withMeta [#_"VSeq" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (VSeq'new meta, (:v this), (:i this))
        )
    )

    (defn #_"seq" VSeq''seq [#_"VSeq" this]
        this
    )

    (defn #_"Object" VSeq''first [#_"VSeq" this]
        (nth (:v this) (:i this))
    )

    (defn #_"seq" VSeq''next [#_"VSeq" this]
        (when (< (inc (:i this)) (count (:v this)))
            (VSeq'new (:v this), (inc (:i this)))
        )
    )

    (defn #_"int" VSeq''count [#_"VSeq" this]
        (- (count (:v this)) (:i this))
    )

    (defm VSeq IMeta
        (IMeta'''meta => :_meta)
    )

    (defm VSeq IObj
        (IObj'''withMeta => VSeq''withMeta)
    )

    (defm VSeq Sequential)

    (defm VSeq Seqable
        (Seqable'''seq => VSeq''seq)
    )

    (defm VSeq ISeq
        (ISeq'''first => VSeq''first)
        (ISeq'''next => VSeq''next)
    )

    (defm VSeq Counted
        (Counted'''count => VSeq''count)
    )

    (defm VSeq IObject
        (IObject'''equals => ASeq''equals)
    )
)

(about #_"RSeq"
    (declare RSeq''seq RSeq''first RSeq''next)

    (defq RSeq [#_"meta" _meta, #_"vector" v, #_"int" i] SeqForm
        clojure.lang.ISeq (seq [_] (RSeq''seq _)) (first [_] (RSeq''first _)) (next [_] (RSeq''next _)) (more [_] (or (RSeq''next _) ()))
    )

    #_inherit
    (defm RSeq ASeq)

    (defn #_"RSeq" RSeq'new
        ([#_"vector" v, #_"int" i] (RSeq'new nil, v, i))
        ([#_"meta" meta, #_"vector" v, #_"int" i]
            (new* RSeq'class (anew [meta, v, i]))
        )
    )

    (defn #_"RSeq" RSeq''withMeta [#_"RSeq" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (RSeq'new meta, (:v this), (:i this))
        )
    )

    (defn #_"seq" RSeq''seq [#_"RSeq" this]
        this
    )

    (defn #_"Object" RSeq''first [#_"RSeq" this]
        (nth (:v this) (:i this))
    )

    (defn #_"seq" RSeq''next [#_"RSeq" this]
        (when (pos? (:i this))
            (RSeq'new (:v this), (dec (:i this)))
        )
    )

    (defn #_"int" RSeq''count [#_"RSeq" this]
        (inc (:i this))
    )

    (defm RSeq IMeta
        (IMeta'''meta => :_meta)
    )

    (defm RSeq IObj
        (IObj'''withMeta => RSeq''withMeta)
    )

    (defm RSeq Sequential)

    (defm RSeq Seqable
        (Seqable'''seq => RSeq''seq)
    )

    (defm RSeq ISeq
        (ISeq'''first => RSeq''first)
        (ISeq'''next => RSeq''next)
    )

    (defm RSeq Counted
        (Counted'''count => RSeq''count)
    )

    (defm RSeq IObject
        (IObject'''equals => ASeq''equals)
    )
)
)

(about #_"beagle.AMapEntry"

(about #_"AMapEntry"
    (defn #_"Object" AMapEntry''nth
        ([#_"AMapEntry" this, #_"int" i]
            (case! i 0 (IMapEntry'''key this) 1 (IMapEntry'''val this) (throw! "index is out of bounds"))
        )
        ([#_"AMapEntry" this, #_"int" i, #_"value" not-found]
            (case! i 0 (IMapEntry'''key this) 1 (IMapEntry'''val this) not-found)
        )
    )

    (defn #_"int" AMapEntry''count [#_"AMapEntry" this]
        2
    )

    (defn #_"seq" AMapEntry''seq [#_"AMapEntry" this]
        (VSeq'new this, 0)
    )

    (defn #_"seq" AMapEntry''rseq [#_"AMapEntry" this]
        (RSeq'new this, 1)
    )

    (defn #_"boolean" AMapEntry''equals [#_"AMapEntry" this, #_"Object" that]
        (or (identical? this that)
            (cond
                (vector? that)
                    (and (= (count that) 2) (= (nth that 0) (IMapEntry'''key this)) (= (nth that 1) (IMapEntry'''val this)))
                (sequential? that)
                    (loop-when [#_"int" i 0 #_"seq" s (seq that)] (< i 2) => (nil? s)
                        (recur-when (and (some? s) (= (Indexed'''nth this, i) (first s))) [(inc i) (next s)] => false)
                    )
                :else
                    false
            )
        )
    )
)
)

(about #_"beagle.MapEntry"

(about #_"MapEntry"
    (defq MapEntry [#_"key" k, #_"value" v] VecForm
        java.util.Map$Entry (getKey [_] (:k _)) (getValue [_] (:v _))
    )

    #_inherit
    (defm MapEntry AMapEntry APersistentVector AFn)

    (defn #_"MapEntry" MapEntry'new [#_"key" k, #_"value" v]
        (new* MapEntry'class (anew [k, v]))
    )

    (defm MapEntry IMapEntry
        (IMapEntry'''key => :k)
        (IMapEntry'''val => :v)
    )

    (defm MapEntry Sequential)

    (defm MapEntry Indexed
        (Indexed'''nth => AMapEntry''nth)
    )

    (defm MapEntry Counted
        (Counted'''count => AMapEntry''count)
    )

    (defm MapEntry Seqable
        (Seqable'''seq => AMapEntry''seq)
    )

    (defm MapEntry Reversible
        (Reversible'''rseq => AMapEntry''rseq)
    )

    (defm MapEntry IObject
        (IObject'''equals => AMapEntry''equals)
    )
)
)

(about #_"beagle.PersistentList"

(about #_"EmptyList"
    (declare EmptyList''seq EmptyList''first EmptyList''next EmptyList''conj EmptyList''empty EmptyList''equals)

    (defq EmptyList [#_"meta" _meta] SeqForm
        clojure.lang.ISeq (seq [_] (EmptyList''seq _)) (first [_] (EmptyList''first _)) (next [_] (EmptyList''next _)) (more [_] (or (EmptyList''next _) ()))
        clojure.lang.IPersistentCollection (cons [_, o] (EmptyList''conj _, o)) (empty [_] (EmptyList''empty _)) (equiv [_, o] (EmptyList''equals _, o))
    )

    (defn #_"EmptyList" EmptyList'new [#_"meta" meta]
        (new* EmptyList'class (anew [meta]))
    )

    (defn #_"EmptyList" EmptyList''withMeta [#_"EmptyList" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (EmptyList'new meta)
        )
    )

    (defn #_"boolean" EmptyList''equals [#_"EmptyList" this, #_"Object" that]
        (and (sequential? that) (nil? (seq that)))
    )

    (defn #_"seq" EmptyList''seq [#_"EmptyList" this]
        nil
    )

    (defn #_"Object" EmptyList''first [#_"EmptyList" this]
        nil
    )

    (defn #_"seq" EmptyList''next [#_"EmptyList" this]
        nil
    )

    (defn #_"int" EmptyList''count [#_"EmptyList" this]
        0
    )

    (declare PersistentList'new)

    (defn #_"PersistentList" EmptyList''conj [#_"EmptyList" this, #_"Object" o]
        (PersistentList'new (:_meta this), o, nil, 1)
    )

    (defn #_"EmptyList" EmptyList''empty [#_"EmptyList" this]
        this
    )

    (defn #_"Object" EmptyList''peek [#_"EmptyList" this]
        nil
    )

    (defn #_"IPersistentList" EmptyList''pop [#_"EmptyList" this]
        (throw! "can't pop the empty list")
    )

    (defm EmptyList IPersistentList Sequential)

    (defm EmptyList IMeta
        (IMeta'''meta => :_meta)
    )

    (defm EmptyList IObj
        (IObj'''withMeta => EmptyList''withMeta)
    )

    (defm EmptyList IObject
        (IObject'''equals => EmptyList''equals)
    )

    (defm EmptyList Seqable
        (Seqable'''seq => EmptyList''seq)
    )

    (defm EmptyList ISeq
        (ISeq'''first => EmptyList''first)
        (ISeq'''next => EmptyList''next)
    )

    (defm EmptyList Counted
        (Counted'''count => EmptyList''count)
    )

    (defm EmptyList IPersistentCollection
        (IPersistentCollection'''conj => EmptyList''conj)
        (IPersistentCollection'''empty => EmptyList''empty)
    )

    (defm EmptyList IPersistentStack
        (IPersistentStack'''peek => EmptyList''peek)
        (IPersistentStack'''pop => EmptyList''pop)
    )
)

(about #_"PersistentList"
    (declare PersistentList''seq PersistentList''conj PersistentList''empty)

    (defq PersistentList [#_"meta" _meta, #_"Object" car, #_"IPersistentList" cdr, #_"int" cnt] SeqForm
        clojure.lang.ISeq (seq [_] (PersistentList''seq _)) (first [_] (:car _)) (next [_] (:cdr _)) (more [_] (or (:cdr _) ()))
        clojure.lang.IPersistentCollection (cons [_, o] (PersistentList''conj _, o)) (empty [_] (PersistentList''empty _)) (equiv [_, o] (ASeq''equals _, o)) (count [_] (:cnt _))
    )

    #_inherit
    (defm PersistentList ASeq)

    (defn #_"PersistentList" PersistentList'new
        ([#_"Object" car] (PersistentList'new nil, car, nil, 1))
        ([#_"meta" meta, #_"Object" car, #_"IPersistentList" cdr, #_"int" cnt]
            (new* PersistentList'class (anew [meta, car, cdr, cnt]))
        )
    )

    (def #_"EmptyList" PersistentList'EMPTY (EmptyList'new nil))

    (declare reverse)

    (defn #_"PersistentList" PersistentList'create [#_"Reversible" init]
        (into PersistentList'EMPTY (if (satisfies? Reversible init) (rseq init) (reverse init)))
    )

    (defn #_"PersistentList" PersistentList''withMeta [#_"PersistentList" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (PersistentList'new meta, (:car this), (:cdr this), (:cnt this))
        )
    )

    (defn #_"seq" PersistentList''seq [#_"PersistentList" this]
        this
    )

    (defn #_"PersistentList" PersistentList''conj [#_"PersistentList" this, #_"Object" o]
        (PersistentList'new (:_meta this), o, this, (inc (:cnt this)))
    )

    (defn #_"PersistentList" PersistentList''empty [#_"PersistentList" this]
        (with-meta PersistentList'EMPTY (:_meta this))
    )

    (defn #_"IPersistentList" PersistentList''pop [#_"PersistentList" this]
        (or (:cdr this) (with-meta PersistentList'EMPTY (:_meta this)))
    )

    (defm PersistentList IPersistentList Sequential)

    (defm PersistentList IMeta
        (IMeta'''meta => :_meta)
    )

    (defm PersistentList IObj
        (IObj'''withMeta => PersistentList''withMeta)
    )

    (defm PersistentList Seqable
        (Seqable'''seq => PersistentList''seq)
    )

    (defm PersistentList ISeq
        (ISeq'''first => :car)
        (ISeq'''next => :cdr)
    )

    (defm PersistentList Counted
        (Counted'''count => :cnt)
    )

    (defm PersistentList IPersistentCollection
        (IPersistentCollection'''conj => PersistentList''conj)
        (IPersistentCollection'''empty => PersistentList''empty)
    )

    (defm PersistentList IPersistentStack
        (IPersistentStack'''peek => :car)
        (IPersistentStack'''pop => PersistentList''pop)
    )

    (defm PersistentList IObject
        (IObject'''equals => ASeq''equals)
    )
)

(defn list
    ([] PersistentList'EMPTY)
    ([& s] (PersistentList'create s))
)

(defn reverse [s] (into (list) s))
)

(about #_"beagle.PersistentMap"

(about #_"MSeq"
    (declare MSeq''seq MSeq''first MSeq''next)

    (defq MSeq [#_"meta" _meta, #_"array" a, #_"int" i] SeqForm
        clojure.lang.ISeq (seq [_] (MSeq''seq _)) (first [_] (MSeq''first _)) (next [_] (MSeq''next _)) (more [_] (or (MSeq''next _) ()))
    )

    #_inherit
    (defm MSeq ASeq)

    (defn #_"MSeq" MSeq'new
        ([#_"array" a, #_"int" i] (MSeq'new nil, a, i))
        ([#_"meta" meta, #_"array" a, #_"int" i]
            (new* MSeq'class (anew [meta, a, i]))
        )
    )

    (defn #_"MSeq" MSeq''withMeta [#_"MSeq" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (MSeq'new meta, (:a this), (:i this))
        )
    )

    (defn #_"seq" MSeq''seq [#_"MSeq" this]
        this
    )

    (defn #_"pair" MSeq''first [#_"MSeq" this]
        (MapEntry'new (aget (:a this) (:i this)), (aget (:a this) (inc (:i this))))
    )

    (defn #_"seq" MSeq''next [#_"MSeq" this]
        (when (< (+ (:i this) 2) (alength (:a this)))
            (MSeq'new (:a this), (+ (:i this) 2))
        )
    )

    (defn #_"int" MSeq''count [#_"MSeq" this]
        (>> (- (alength (:a this)) (:i this)) 1)
    )

    (defm MSeq IMeta
        (IMeta'''meta => :_meta)
    )

    (defm MSeq IObj
        (IObj'''withMeta => MSeq''withMeta)
    )

    (defm MSeq Sequential)

    (defm MSeq Seqable
        (Seqable'''seq => MSeq''seq)
    )

    (defm MSeq ISeq
        (ISeq'''first => MSeq''first)
        (ISeq'''next => MSeq''next)
    )

    (defm MSeq Counted
        (Counted'''count => MSeq''count)
    )

    (defm MSeq IObject
        (IObject'''equals => ASeq''equals)
    )
)

(about #_"PersistentMap"
    (declare PersistentMap''seq PersistentMap''assoc PersistentMap''containsKey)

    (defq PersistentMap [#_"meta" _meta, #_"array" array] MapForm
        clojure.lang.Seqable (seq [_] (PersistentMap''seq _))
        clojure.lang.Associative (assoc [_, key, val] (PersistentMap''assoc _, key, val)) (containsKey [_, key] (PersistentMap''containsKey _, key))
    )

    #_inherit
    (defm PersistentMap AFn)

    (defn #_"PersistentMap" PersistentMap'new
        ([#_"array" a] (PersistentMap'new nil, a))
        ([#_"meta" meta, #_"array" a]
            (new* PersistentMap'class (anew [meta, (or a (anew 0))]))
        )
    )

    (def #_"PersistentMap" PersistentMap'EMPTY (PersistentMap'new nil))

    (defn #_"PersistentMap" PersistentMap''create [#_"PersistentMap" this, #_"array" init]
        (PersistentMap'new (:_meta this), init)
    )

    (defn #_"PersistentMap" PersistentMap'createWithCheck [#_"array" init]
        (loop-when-recur [#_"int" i 0] (< i (alength init)) [(+ i 2)]
            (loop-when-recur [#_"int" j (+ i 2)] (< j (alength init)) [(+ j 2)]
                (when (= (aget init i) (aget init j))
                    (throw! (str "duplicate key: " (aget init i)))
                )
            )
        )
        (PersistentMap'new init)
    )

    (defn #_"PersistentMap" PersistentMap'createAsIfByAssoc [#_"array" init]
        (when (odd? (alength init))
            (throw! (str "no value supplied for key: " (aget init (dec (alength init)))))
        )
        (let [#_"int" n
                (loop-when [n 0 #_"int" i 0] (< i (alength init)) => n
                    (let [#_"boolean" dup?
                            (loop-when [dup? false #_"int" j 0] (< j i) => dup?
                                (or (= (aget init i) (aget init j))
                                    (recur dup? (+ j 2))
                                )
                            )]
                        (recur (if dup? n (+ n 2)) (+ i 2))
                    )
                )
              init
                (when (< n (alength init)) => init
                    (let [#_"array" nodups (anew n)
                          #_"int" m
                            (loop-when [m 0 #_"int" i 0] (< i (alength init)) => m
                                (let [#_"boolean" dup?
                                        (loop-when [dup? false #_"int" j 0] (< j m) => dup?
                                            (or (= (aget init i) (aget nodups j))
                                                (recur dup? (+ j 2))
                                            )
                                        )
                                      m (when-not dup? => m
                                            (let [#_"int" j
                                                    (loop-when [j (- (alength init) 2)] (<= i j) => j
                                                        (if (= (aget init i) (aget init j))
                                                            j
                                                            (recur (- j 2))
                                                        )
                                                    )]
                                                (aset! nodups m (aget init i))
                                                (aset! nodups (inc m) (aget init (inc j)))
                                                (+ m 2)
                                            )
                                        )]
                                    (recur m (+ i 2))
                                )
                            )]
                        (when (= m n) => (throw! (str "internal error: m=" m))
                            nodups
                        )
                    )
                )]
            (PersistentMap'new init)
        )
    )

    (defn #_"PersistentMap" PersistentMap''withMeta [#_"PersistentMap" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (PersistentMap'new meta, (:array this))
        )
    )

    (defn #_"int" PersistentMap''count [#_"PersistentMap" this]
        (>> (alength (:array this)) 1)
    )

    (defn #_"int" PersistentMap'index-of [#_"array" a, #_"key" key]
        (loop-when [#_"int" i 0] (< i (alength a)) => -1
            (if (= (aget a i) key) i (recur (+ i 2)))
        )
    )

    (defn #_"value" PersistentMap''valAt
        ([#_"PersistentMap" this, #_"key" key] (PersistentMap''valAt this, key, nil))
        ([#_"PersistentMap" this, #_"key" key, #_"value" not-found]
            (let [
                #_"array" a (:array this) #_"int" i (PersistentMap'index-of a, key)
            ]
                (if (< -1 i) (aget a (inc i)) not-found)
            )
        )
    )

    (defn #_"Object" PersistentMap''invoke
        ([#_"PersistentMap" this, #_"key" key] (get this key))
        ([#_"PersistentMap" this, #_"key" key, #_"value" not-found] (get this key not-found))
    )

    (defn #_"IPersistentMap" PersistentMap''assoc [#_"PersistentMap" this, #_"key" key, #_"value" val]
        (let [
            #_"array" a (:array this) #_"int" i (PersistentMap'index-of a, key)
        ]
            (if (< -1 i)
                (if (= (aget a (inc i)) val)
                    this
                    (PersistentMap''create this, (-> (aclone a) (aset! (inc i) val)))
                )
                (let [
                    #_"int" n (alength a)
                    #_"array" a' (anew (+ n 2))
                    a' (if (pos? n) (acopy! a' 0 a 0 n) a')
                ]
                    (PersistentMap''create this, (-> a' (aset! n key) (aset! (inc n) val)))
                )
            )
        )
    )

    (defn #_"boolean" PersistentMap''containsKey [#_"PersistentMap" this, #_"key" key]
        (< -1 (PersistentMap'index-of (:array this), key))
    )

    (defn #_"pair" PersistentMap''entryAt [#_"PersistentMap" this, #_"key" key]
        (let [
            #_"array" a (:array this) #_"int" i (PersistentMap'index-of a, key)
        ]
            (when (< -1 i)
                (MapEntry'new (aget a i), (aget a (inc i)))
            )
        )
    )

    (defn #_"IPersistentMap" PersistentMap''dissoc [#_"PersistentMap" this, #_"key" key]
        (let [
            #_"array" a (:array this) #_"int" i (PersistentMap'index-of a, key)
        ]
            (when (< -1 i) => this
                (let-when [#_"int" n (- (alength a) 2)] (pos? n) => (with-meta PersistentMap'EMPTY (:_meta this))
                    (let [
                        #_"array" a' (-> (anew n) (acopy! 0 a 0 i) (acopy! i a (+ i 2) (- n i)))
                    ]
                        (PersistentMap''create this, a')
                    )
                )
            )
        )
    )

    (defn #_"IPersistentCollection" PersistentMap''conj [#_"PersistentMap" this, #_"Object" o]
        (condp satisfies? o
            IMapEntry
                (assoc this (key o) (val o))
            IPersistentVector
                (when (= (count o) 2) => (throw! "vector arg to map conj must be a pair")
                    (assoc this (nth o 0) (nth o 1))
                )
            #_else
                (loop-when [this this #_"seq" s (seq o)] (some? s) => this
                    (let [#_"pair" e (first s)]
                        (recur (assoc this (key e) (val e)) (next s))
                    )
                )
        )
    )

    (defn #_"IPersistentMap" PersistentMap''empty [#_"PersistentMap" this]
        (with-meta PersistentMap'EMPTY (:_meta this))
    )

    (defn #_"seq" PersistentMap''seq [#_"PersistentMap" this]
        (when (pos? (alength (:array this)))
            (MSeq'new (:array this), 0)
        )
    )

    (declare contains?)

    (defn #_"boolean" PersistentMap''equals [#_"PersistentMap" this, #_"Object" that]
        (or (identical? this that)
            (and (map? that) (= (count that) (count this))
                (loop-when [#_"seq" s (seq this)] (some? s) => true
                    (let [#_"pair" e (first s) #_"Object" k (key e)]
                        (and (contains? that k) (= (val e) (get that k))
                            (recur (next s))
                        )
                    )
                )
            )
        )
    )

    (defm PersistentMap IMeta
        (IMeta'''meta => :_meta)
    )

    (defm PersistentMap IObj
        (IObj'''withMeta => PersistentMap''withMeta)
    )

    (defm PersistentMap Counted
        (Counted'''count => PersistentMap''count)
    )

    (defm PersistentMap ILookup
        (ILookup'''valAt => PersistentMap''valAt)
    )

    (defm PersistentMap IFn
        (IFn'''invoke => PersistentMap''invoke)
        (IFn'''applyTo => AFn'applyTo)
    )

    (defm PersistentMap Associative
        (Associative'''assoc => PersistentMap''assoc)
        (Associative'''containsKey => PersistentMap''containsKey)
        (Associative'''entryAt => PersistentMap''entryAt)
    )

    (defm PersistentMap IPersistentMap
        (IPersistentMap'''dissoc => PersistentMap''dissoc)
    )

    (defm PersistentMap IPersistentCollection
        (IPersistentCollection'''conj => PersistentMap''conj)
        (IPersistentCollection'''empty => PersistentMap''empty)
    )

    (defm PersistentMap Seqable
        (Seqable'''seq => PersistentMap''seq)
    )

    (defm PersistentMap IObject
        (IObject'''equals => PersistentMap''equals)
    )
)

(defn array-map
    ([] PersistentMap'EMPTY)
    ([& keyvals] (PersistentMap'createAsIfByAssoc (anew keyvals)))
)
)

(about #_"beagle.PersistentSet"

(about #_"PersistentSet"
    (declare PersistentSet''invoke)

    (defq PersistentSet [#_"meta" _meta, #_"map" impl] SetForm
        clojure.lang.IFn (invoke [_, a] (PersistentSet''invoke _, a))
    )

    #_inherit
    (defm PersistentSet AFn)

    (defn #_"PersistentSet" PersistentSet'new [#_"meta" meta, #_"map" impl]
        (new* PersistentSet'class (anew [meta, impl]))
    )

    (def #_"PersistentSet" PersistentSet'EMPTY (PersistentSet'new nil, PersistentMap'EMPTY))

    (defn #_"PersistentSet" PersistentSet'create [#_"Seqable" init]
        (into PersistentSet'EMPTY init)
    )

    (defn #_"PersistentSet" PersistentSet'createWithCheck [#_"Seqable" init]
        (let [#_"PersistentSet" s PersistentSet'EMPTY]
            (loop-when [s s #_"seq" q (seq init) #_"int" n 0] (some? q) => s
                (let [s (conj s (first q))]
                    (when (= (count s) (inc n)) => (throw! (str "duplicate key: " (first q)))
                        (recur s (next q) (inc n))
                    )
                )
            )
        )
    )

    (defn #_"PersistentSet" PersistentSet''withMeta [#_"PersistentSet" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (PersistentSet'new meta, (:impl this))
        )
    )

    (defn #_"int" PersistentSet''count [#_"PersistentSet" this]
        (count (:impl this))
    )

    (defn #_"PersistentSet" PersistentSet''conj [#_"PersistentSet" this, #_"value" val]
        (if (contains? (:impl this) val)
            this
            (PersistentSet'new (:_meta this), (assoc (:impl this) val val))
        )
    )

    (defn #_"PersistentSet" PersistentSet''empty [#_"PersistentSet" this]
        (with-meta PersistentSet'EMPTY (:_meta this))
    )

    (defn #_"IPersistentSet" PersistentSet''disj [#_"PersistentSet" this, #_"key" key]
        (if (contains? (:impl this) key)
            (PersistentSet'new (:_meta this), (dissoc (:impl this) key))
            this
        )
    )

    (defn #_"boolean" PersistentSet''contains? [#_"PersistentSet" this, #_"key" key]
        (contains? (:impl this) key)
    )

    (defn #_"value" PersistentSet''get [#_"PersistentSet" this, #_"key" key]
        (get (:impl this) key)
    )

    (defn #_"seq" PersistentSet''seq [#_"PersistentSet" this]
        (keys (:impl this))
    )

    (defn #_"Object" PersistentSet''invoke
        ([#_"PersistentSet" this, #_"key" key] (get this key))
        ([#_"PersistentSet" this, #_"key" key, #_"value" not-found] (get this key not-found))
    )

    (defn #_"boolean" PersistentSet''equals [#_"PersistentSet" this, #_"Object" that]
        (or (identical? this that)
            (and (set? that) (= (count this) (count that))
                (loop-when [#_"seq" s (seq that)] (some? s) => true
                    (and (contains? this (first s)) (recur (next s)))
                )
            )
        )
    )

    (defm PersistentSet IMeta
        (IMeta'''meta => :_meta)
    )

    (defm PersistentSet IObj
        (IObj'''withMeta => PersistentSet''withMeta)
    )

    (defm PersistentSet Counted
        (Counted'''count => PersistentSet''count)
    )

    (defm PersistentSet IPersistentCollection
        (IPersistentCollection'''conj => PersistentSet''conj)
        (IPersistentCollection'''empty => PersistentSet''empty)
    )

    (defm PersistentSet IPersistentSet
        (IPersistentSet'''disj => PersistentSet''disj)
        (IPersistentSet'''contains? => PersistentSet''contains?)
        (IPersistentSet'''get => PersistentSet''get)
    )

    (defm PersistentSet Seqable
        (Seqable'''seq => PersistentSet''seq)
    )

    (defm PersistentSet IFn
        (IFn'''invoke => PersistentSet''invoke)
        (IFn'''applyTo => AFn'applyTo)
    )

    (defm PersistentSet IObject
        (IObject'''equals => PersistentSet''equals)
    )
)

(defn array-set
    ([] PersistentSet'EMPTY)
    ([& keys] (PersistentSet'create keys))
)

(defn set [s] (if (set? s) (with-meta s nil) (into (array-set) s)))
)

(about #_"beagle.PersistentVector"

(about #_"VNode"
    (defq VNode [#_"thread'" edit, #_"array" array, #_"index" index])

    (defn #_"node" VNode'new [#_"thread'" edit, #_"array" array, #_"index" index]
        (new* VNode'class (anew [edit, (or array (anew 32)), index]))
    )

    (def #_"node" VNode'EMPTY (VNode'new nil, nil, nil))

    (defn #_"values" VNode''array-for
        ([#_"node" this, #_"int" i, #_"int" shift, #_"int" cnt] (VNode''array-for this, i, shift, cnt, cnt, nil))
        ([#_"node" this, #_"int" i, #_"int" shift, #_"int" cnt, #_"int" tail-off, #_"values" tail]
            (when (< -1 i cnt) => (throw! "index is out of bounds")
                (when (< i tail-off) => tail
                    (loop-when [i i #_"node" node this shift shift] (pos? shift) => (:array node)
                        (let [
                            #_"index" x (:index node)
                            #_"int" m (& (>> i shift) 31)
                            [m i]
                                (when (some? x) => [m i]
                                    (let [
                                        m (loop-when-recur m (<= (aget x m) i) (inc m) => m)
                                    ]
                                        [m (if (pos? m) (- i (aget x (dec m))) i)]
                                    )
                                )
                        ]
                            (recur i (aget (:array node) m) (- shift 5))
                        )
                    )
                )
            )
        )
    )

    (defn #_"value" VNode''value-for [#_"node" this, #_"int" i, #_"int" shift, #_"int" cnt, #_"int" tail-off, #_"values" tail]
        (when (< -1 i cnt) => (throw! "index is out of bounds")
            (when (< i tail-off) => (aget tail (- i tail-off))
                (loop-when [i i #_"node" node this shift shift] (pos? shift) => (aget (:array node) (& (>> i shift) 31))
                    (let [
                        #_"index" x (:index node)
                        #_"int" m (& (>> i shift) 31)
                        [m i]
                            (when (some? x) => [m i]
                                (let [
                                    m (loop-when-recur m (<= (aget x m) i) (inc m) => m)
                                ]
                                    [m (if (pos? m) (- i (aget x (dec m))) i)]
                                )
                            )
                    ]
                        (recur i (aget (:array node) m) (- shift 5))
                    )
                )
            )
        )
    )

    (defn #_"node" VNode''new-path [#_"node" this, #_"thread'" edit, #_"int" shift]
        (when (pos? shift) => this
            (VNode'new edit, (-> (anew 32) (aset! 0 (VNode''new-path this, edit, (- shift 5)))), nil)
        )
    )

    (defn #_"int" VNode'last-range [#_"index" x]
        (aget x (dec (aget x 32)))
    )

    (defn #_"boolean" VNode''overflow? [#_"node" this, #_"int" shift, #_"int" cnt]
        (let [
            #_"index" x (:index this)
        ]
            (when (some? x) => (< (<< 1 shift) (>> (inc cnt) 5))
                (and (= (aget x 32) 32)
                    (or (= shift 5)
                        (recur
                            (aget (:array this) 31)
                            (- shift 5)
                            (+ (- (aget x 31) (aget x 30)) 32)
                        )
                    )
                )
            )
        )
    )

    (defn #_"node" VNode''push-tail [#_"node" this, #_"thread'" edit, #_"int" shift, #_"int" cnt, #_"node" tail-node]
        (let [
            #_"array" a (:array this) #_"index" x (:index this)
        ]
            (if (some? x)
                (let [
                    #_"int" e (dec (aget x 32))
                    #_"node" child
                        (when (< 5 shift)
                            (let [
                                #_"int" n (if (pos? e) (- (aget x e) (aget x (dec e))) (aget x 0))
                            ]
                                (when (< n (<< 1 shift))
                                    (VNode''push-tail (aget a e), edit, (- shift 5), (inc n), tail-node)
                                )
                            )
                        )
                    a (if true (aclone a) a) x (if true (aclone x) x)
                    [a x]
                        (if (some? child)
                            [(aset! a e child) (aswap! x e + 32)]
                            (let [
                                a (aset! a (inc e) (VNode''new-path tail-node, edit, (- shift 5)))
                                x (aset! x (inc e) (+ (aget x e) 32))
                            ]
                                [a (aswap! x 32 inc)]
                            )
                        )
                ]
                    (if true (VNode'new edit, a, x) this)
                )
                (let [
                    #_"int" e (& (>> (dec cnt) shift) 31)
                    #_"node" child
                        (when (< 5 shift) => tail-node
                            (if-some [child (aget a e)]
                                (VNode''push-tail child, edit, (- shift 5), cnt, tail-node)
                                (VNode''new-path tail-node, edit, (- shift 5))
                            )
                        )
                    a (if true (aclone a) a)
                    a (aset! a e child)
                ]
                    (if true (VNode'new edit, a, nil) this)
                )
            )
        )
    )

    (defn #_"node" VNode''pop-tail [#_"node" this, #_"thread'" edit, #_"int" shift, #_"int" tail-off]
        (let [
            #_"array" a (:array this) #_"index" x (:index this)
            #_"int" e (& (>> (dec tail-off) shift) 31)
        ]
            (if (some? x)
                (let [
                    e (loop-when-recur e (and (< e 31) (some? (aget x (inc e)))) (inc e) => e)
                ]
                    (cond
                        (< 5 shift)
                            (let [
                                #_"node" child (aget a e)
                                #_"node" child' (VNode''pop-tail child, edit, (- shift 5), (if (pos? e) (- (aget x e) (aget x (dec e))) (aget x 0)))
                            ]
                                (when (or (some? child') (pos? e))
                                    (let [
                                        a (if true (aclone a) a)
                                        a (-> a (aset! e child'))
                                        x (if true (aclone x) x)
                                        x
                                            (if (some? child')
                                                (let [
                                                    #_"int" delta
                                                        (when (some? (:index child)) => 32
                                                            (- (VNode'last-range (:index child)) (VNode'last-range (:index child')))
                                                        )
                                                ]
                                                    (-> x (aswap! e - delta))
                                                )
                                                (-> x (aset! e nil) (aswap! 32 dec))
                                            )
                                    ]
                                        (if true (VNode'new edit, a, x) this)
                                    )
                                )
                            )
                        (pos? e)
                            (let [
                                a (-> (if true (aclone a) a) (aset! e nil))
                                x (-> (if true (aclone x) x) (aset! e nil) (aswap! 32 dec))
                            ]
                                (if true (VNode'new edit, a, x) this)
                            )
                    )
                )
                (cond
                    (< 5 shift)
                        (let [
                            #_"node" child (VNode''pop-tail (aget a e), edit, (- shift 5), tail-off)
                        ]
                            (when (or (some? child) (pos? e))
                                (let [
                                    a (if true (aclone a) a)
                                    a (aset! a e child)
                                ]
                                    (if true (VNode'new edit, a, nil) this)
                                )
                            )
                        )
                    (pos? e)
                        (let [
                            a (if true (aclone a) a)
                            a (aset! a e nil)
                        ]
                            (if true (VNode'new edit, a, nil) this)
                        )
                )
            )
        )
    )

    (defn #_"node" VNode''do-assoc [#_"node" this, #_"thread'" edit, #_"int" shift, #_"int" i, #_"value" val]
        (let [
            #_"array" a (:array this) #_"index" x (:index this)
            a (if true (aclone a) a)
            #_"int" m (& (>> i shift) 31)
            a
                (when (pos? shift) => (aset! a m val)
                    (let [
                        [m i]
                            (when (some? x) => [m i]
                                (let [
                                    m (loop-when-recur m (<= (aget x m) i) (inc m) => m)
                                ]
                                    [m (if (pos? m) (- i (aget x (dec m))) i)]
                                )
                            )
                    ]
                        (aswap! a m VNode''do-assoc edit, (- shift 5), i, val)
                    )
                )
        ]
            (if true (VNode'new edit, a, x) this)
        )
    )
)

(about #_"PersistentVector"
    (declare PersistentVector''seq PersistentVector''rseq PersistentVector''conj PersistentVector''empty PersistentVector''equals PersistentVector''nth PersistentVector''invoke PersistentVector''applyTo)

    (defq PersistentVector [#_"meta" _meta, #_"int" cnt, #_"int" shift, #_"node" root, #_"values" tail] VecForm
        clojure.lang.Seqable (seq [_] (PersistentVector''seq _))
        clojure.lang.Reversible (rseq [_] (PersistentVector''rseq _))
        clojure.lang.IPersistentCollection (cons [_, o] (PersistentVector''conj _, o)) (empty [_] (PersistentVector''empty _)) (equiv [_, o] (PersistentVector''equals _, o))
        clojure.lang.IPersistentVector
        clojure.lang.Counted (count [_] (:cnt _))
        clojure.lang.Indexed (nth [_, i] (PersistentVector''nth _, i)) (nth [_, i, not-found] (PersistentVector''nth _, i, not-found))
        clojure.lang.IFn (invoke [_, a] (PersistentVector''invoke _, a)) (applyTo [_, args] (PersistentVector''applyTo _, args))
    )

    #_inherit
    (defm PersistentVector APersistentVector AFn)

    (defn #_"PersistentVector" PersistentVector'new
        ([#_"int" cnt, #_"int" shift, #_"node" root, #_"values" tail] (PersistentVector'new nil, cnt, shift, root, tail))
        ([#_"meta" meta, #_"int" cnt, #_"int" shift, #_"node" root, #_"values" tail]
            (new* PersistentVector'class (anew [meta, cnt, shift, root, tail]))
        )
    )

    (def #_"PersistentVector" PersistentVector'EMPTY (PersistentVector'new 0, 5, VNode'EMPTY, (anew 0)))

    (defn #_"PersistentVector" PersistentVector'create [& values]
        (when-some [#_"seq" s (seq values)] => PersistentVector'EMPTY
            (let [
                #_"values" tail (anew (take 32 s)) #_"int" n (alength tail)
                #_"PersistentVector" w (PersistentVector'new n, 5, VNode'EMPTY, tail)
            ]
                (when-some [s (seq (drop 32 s))] => w
                    (into w s)
                )
            )
        )
    )

    (defn #_"PersistentVector" PersistentVector''withMeta [#_"PersistentVector" this, #_"meta" meta]
        (when-not (= meta (:_meta this)) => this
            (PersistentVector'new meta, (:cnt this), (:shift this), (:root this), (:tail this))
        )
    )

    (defn #_"boolean" PersistentVector''equals [#_"PersistentVector" this, #_"Object" that]
        (or (identical? this that)
            (cond
                (vector? that)
                    (when (= (:cnt this) (:cnt that)) => false
                        (loop-when [#_"int" i 0] (< i (:cnt this)) => true
                            (recur-when (= (Indexed'''nth this, i) (Indexed'''nth that, i)) [(inc i)] => false)
                        )
                    )
                (sequential? that)
                    (loop-when [#_"int" i 0 #_"seq" s (seq that)] (< i (:cnt this)) => (nil? s)
                        (recur-when (and (some? s) (= (Indexed'''nth this, i) (first s))) [(inc i) (next s)] => false)
                    )
                :else
                    false
            )
        )
    )

    (defn #_"int" PersistentVector''tail-off [#_"PersistentVector" this]
        (- (:cnt this) (alength (:tail this)))
    )

    (defn #_"values" PersistentVector''array-for [#_"PersistentVector" this, #_"int" i]
        (VNode''array-for (:root this), i, (:shift this), (:cnt this), (PersistentVector''tail-off this), (:tail this))
    )

    (defn #_"value" PersistentVector''value-for [#_"PersistentVector" this, #_"int" i]
        (VNode''value-for (:root this), i, (:shift this), (:cnt this), (PersistentVector''tail-off this), (:tail this))
    )

    (defn #_"value" PersistentVector''nth
        ([#_"PersistentVector" this, #_"int" i]
            (PersistentVector''value-for this, i)
        )
        ([#_"PersistentVector" this, #_"int" i, #_"value" not-found]
            (when (< -1 i (:cnt this)) => not-found
                (PersistentVector''value-for this, i)
            )
        )
    )

    (defn #_"PersistentVector" PersistentVector''conj [#_"PersistentVector" this, #_"value" val]
        (let [
            #_"int" tail-len (alength (:tail this))
        ]
            (if (< tail-len 32)
                (let [
                    #_"values" tail (-> (anew (inc tail-len)) (acopy! 0 (:tail this) 0 tail-len) (aset! tail-len val))
                ]
                    (PersistentVector'new (:_meta this), (inc (:cnt this)), (:shift this), (:root this), tail)
                )
                (let [
                    #_"node" tail-node (VNode'new nil, (:tail this), nil)
                    #_"int" shift (:shift this)
                    [#_"node" root shift]
                        (if (VNode''overflow? (:root this), shift, (:cnt this))
                            (let [
                                #_"array" a
                                    (-> (anew 32)
                                        (aset! 0 (:root this))
                                        (aset! 1 (VNode''new-path tail-node, nil, shift))
                                    )
                                #_"index" x
                                    (when (some? (:index (:root this)))
                                        (let [
                                            #_"int" n (aget (:index (:root this)) 31)
                                        ]
                                            (-> (anew 33) (aset! 0 n) (aset! 1 (+ n 32)) (aset! 32 2))
                                        )
                                    )
                            ]
                                [(VNode'new nil, a, x) (+ shift 5)]
                            )
                            [(VNode''push-tail (:root this), nil, shift, (:cnt this), tail-node) shift]
                        )
                ]
                    (PersistentVector'new (:_meta this), (inc (:cnt this)), shift, root, (anew [ val ]))
                )
            )
        )
    )

    (defn #_"PersistentVector" PersistentVector''empty [#_"PersistentVector" this]
        (IObj'''withMeta PersistentVector'EMPTY, (:_meta this))
    )

    (defn #_"PersistentVector" PersistentVector''assocN [#_"PersistentVector" this, #_"int" i, #_"value" val]
        (if (< -1 i (:cnt this))
            (let [
                #_"int" tail-off (PersistentVector''tail-off this)
            ]
                (if (<= tail-off i)
                    (let [
                        #_"int" n (alength (:tail this))
                        #_"values" tail (-> (anew n) (acopy! 0 (:tail this) 0 n) (aset! (- i tail-off) val))
                    ]
                        (PersistentVector'new (:_meta this), (:cnt this), (:shift this), (:root this), tail)
                    )
                    (PersistentVector'new (:_meta this), (:cnt this), (:shift this), (VNode''do-assoc (:root this), nil, (:shift this), i, val), (:tail this))
                )
            )
            (when (= i (:cnt this)) => (throw! "index is out of bounds")
                (IPersistentCollection'''conj this, val)
            )
        )
    )

    (defn #_"value" PersistentVector''peek [#_"PersistentVector" this]
        (when (pos? (:cnt this))
            (Indexed'''nth this, (dec (:cnt this)))
        )
    )

    (defn #_"PersistentVector" PersistentVector''pop [#_"PersistentVector" this]
        (case! (:cnt this)
            0   (throw! "can't pop the empty vector")
            1   (IObj'''withMeta PersistentVector'EMPTY, (:_meta this))
            (let [
                #_"int" tail-len (alength (:tail this))
            ]
                (if (< 1 tail-len)
                    (let [
                        #_"values" tail (-> (anew (dec tail-len)) (acopy! 0 (:tail this) 0 (dec tail-len)))
                    ]
                        (PersistentVector'new (:_meta this), (dec (:cnt this)), (:shift this), (:root this), tail)
                    )
                    (let [
                        #_"values" tail (PersistentVector''array-for this, (- (:cnt this) 2))
                        #_"int" shift (:shift this)
                        #_"node" root (VNode''pop-tail (:root this), nil, shift, (PersistentVector''tail-off this))
                        [shift root]
                            (cond
                                (nil? root)                                     [shift VNode'EMPTY]
                                (and (< 5 shift) (nil? (aget (:array root) 1))) [(- shift 5) (aget (:array root) 0)]
                                :else                                           [shift root]
                            )
                    ]
                        (PersistentVector'new (:_meta this), (dec (:cnt this)), shift, root, tail)
                    )
                )
            )
        )
    )

    (defn #_"value" PersistentVector''invoke [#_"PersistentVector" this, #_"key" arg]
        (when (int? arg) => (throw! "arg must be integer")
            (Indexed'''nth this, (int! arg))
        )
    )

    (defn #_"value" PersistentVector''applyTo [#_"PersistentVector" this, #_"seq" args]
        (case! (count args 1)
            1 (IFn'''invoke this, (first args))
        )
    )

    (defn #_"IPersistentVector" PersistentVector''assoc [#_"PersistentVector" this, #_"key" key, #_"value" val]
        (when (int? key) => (throw! "key must be integer")
            (IPersistentVector'''assocN this, (int! key), val)
        )
    )

    (defn #_"boolean" PersistentVector''containsKey [#_"PersistentVector" this, #_"key" key]
        (and (int? key) (< -1 (int! key) (:cnt this)))
    )

    (defn #_"pair" PersistentVector''entryAt [#_"PersistentVector" this, #_"key" key]
        (when (int? key)
            (let-when [#_"int" i (int! key)] (< -1 i (:cnt this))
                (MapEntry'new key, (Indexed'''nth this, i))
            )
        )
    )

    (defn #_"value" PersistentVector''valAt
        ([#_"PersistentVector" this, #_"key" key] (PersistentVector''valAt this, key, nil))
        ([#_"PersistentVector" this, #_"key" key, #_"value" not-found]
            (when (int? key) => not-found
                (let-when [#_"int" i (int! key)] (< -1 i (:cnt this)) => not-found
                    (PersistentVector''value-for this, i)
                )
            )
        )
    )

    (defn #_"seq" PersistentVector''seq [#_"PersistentVector" this]
        (when (pos? (:cnt this))
            (VSeq'new this, 0)
        )
    )

    (defn #_"seq" PersistentVector''rseq [#_"PersistentVector" this]
        (when (pos? (:cnt this))
            (RSeq'new this, (dec (:cnt this)))
        )
    )

    (defm PersistentVector IMeta
        (IMeta'''meta => :_meta)
    )

    (defm PersistentVector IObj
        (IObj'''withMeta => PersistentVector''withMeta)
    )

    (defm PersistentVector IObject
        (IObject'''equals => PersistentVector''equals)
    )

    (defm PersistentVector Counted
        (Counted'''count => :cnt)
    )

    (defm PersistentVector Indexed
        (Indexed'''nth => PersistentVector''nth)
    )

    (defm PersistentVector IPersistentCollection
        (IPersistentCollection'''conj => PersistentVector''conj)
        (IPersistentCollection'''empty => PersistentVector''empty)
    )

    (defm PersistentVector IPersistentVector
        (IPersistentVector'''assocN => PersistentVector''assocN)
    )

    (defm PersistentVector IPersistentStack
        (IPersistentStack'''peek => PersistentVector''peek)
        (IPersistentStack'''pop => PersistentVector''pop)
    )

    (defm PersistentVector IFn
        (IFn'''invoke => PersistentVector''invoke)
        (IFn'''applyTo => PersistentVector''applyTo)
    )

    (defm PersistentVector Associative
        (Associative'''assoc => PersistentVector''assoc)
        (Associative'''containsKey => PersistentVector''containsKey)
        (Associative'''entryAt => PersistentVector''entryAt)
    )

    (defm PersistentVector ILookup
        (ILookup'''valAt => PersistentVector''valAt)
    )

    (defm PersistentVector Sequential)

    (defm PersistentVector Seqable
        (Seqable'''seq => PersistentVector''seq)
    )

    (defm PersistentVector Reversible
        (Reversible'''rseq => PersistentVector''rseq)
    )
)

(defn vector
    ([]                   PersistentVector'EMPTY)
    ([a]                 (PersistentVector'create a))
    ([a b]               (PersistentVector'create a b))
    ([a b c]             (PersistentVector'create a b c))
    ([a b c d]           (PersistentVector'create a b c d))
    ([a b c d & s] (apply PersistentVector'create a b c d s))
)

(defn vec [s]
    (if (vector? s) s (apply vector s))
)
)

(about #_"beagle.RT"

(about #_"RT"
    (defn #_"Object" RT'get
        ([#_"Object" coll, #_"key" key]
            (cond
                (satisfies? ILookup coll)
                    (ILookup'''valAt coll, key)
                (nil? coll)
                    nil
                (set? coll)
                    (IPersistentSet'''get coll, key)
                (and (number? key) (or (string? coll) (array? coll)))
                    (let-when [#_"int" n (int! key)] (< -1 n (count coll))
                        (nth coll n)
                    )
                (clojure-ilookup? coll)
                    (ILookup''valAt coll, key)
            )
        )
        ([#_"Object" coll, #_"key" key, #_"value" not-found]
            (cond
                (satisfies? ILookup coll)
                    (ILookup'''valAt coll, key, not-found)
                (nil? coll)
                    not-found
                (set? coll)
                    (if (contains? coll key) (IPersistentSet'''get coll, key) not-found)
                (and (number? key) (or (string? coll) (array? coll)))
                    (let [#_"int" n (int! key)]
                        (if (< -1 n (count coll)) (nth coll n) not-found)
                    )
                (clojure-ilookup? coll)
                    (ILookup''valAt coll, key, not-found)
                :else
                    not-found
            )
        )
    )

(defn get
    ([coll key          ] (RT'get coll key          ))
    ([coll key not-found] (RT'get coll key not-found))
)

(defn get-in
    ([m ks] (reduce get m ks))
    ([m ks not-found]
        (loop-when [m m o (anew 0) ks (seq ks)] ks => m
            (let-when [m (get m (first ks) o)] (identical? m o) => (recur m o (next ks))
                not-found
            )
        )
    )
)

    (defn #_"Object" RT'contains [#_"Object" coll, #_"key" key]
        (cond
            (nil? coll)
                false
            (associative? coll)
                (if (Associative'''containsKey coll, key) true false)
            (set? coll)
                (if (IPersistentSet'''contains? coll, key) true false)
            (and (number? key) (or (string? coll) (array? coll)))
                (let [#_"int" n (int! key)]
                    (if (< -1 n (count coll)) true false)
                )
            :else
                (throw! (str "contains? not supported on " coll))
        )
    )

(defn contains? [coll key] (RT'contains coll key))

    (defn #_"Object" RT'find [#_"Object" coll, #_"key" key]
        (cond
            (nil? coll)
                nil
            (associative? coll)
                (Associative'''entryAt coll, key)
            :else
                (throw! (str "find not supported on " coll))
        )
    )

(defn find [m k] (RT'find m k))

    (defn #_"seq" RT'findKey [#_"Keyword" key, #_"seq" keyvals]
        (loop-when keyvals (some? keyvals)
            (when-some [#_"seq" s (next keyvals)] => (throw! "malformed keyword argslist")
                (when-not (= (first keyvals) key) => s
                    (recur (next s))
                )
            )
        )
    )

    (defn #_"Object" RT'nth
        ([#_"Object" coll, #_"int" n]
            (cond
                (indexed? coll)
                    (Indexed'''nth coll, n)
                (nil? coll)
                    nil
                (string? coll)
                    (Character'valueOf (String''charAt coll, n))
                (array? coll)
                    (Array'get coll, n)
                (matcher? coll)
                    (Matcher''group coll, n)
                (map-entry? coll)
                    (let [#_"pair" e coll]
                        (case! n 0 (key e) 1 (val e) (throw! "index is out of bounds"))
                    )
                (sequential? coll)
                    (loop-when [#_"int" i 0 #_"seq" s (seq coll)] (and (<= i n) (some? s)) => (throw! "index is out of bounds")
                        (recur-when (< i n) [(inc i) (next s)] => (first s))
                    )
                :else
                    (throw! (str "nth not supported on " coll))
            )
        )
        ([#_"Object" coll, #_"int" n, #_"value" not-found]
            (cond
                (indexed? coll)
                    (Indexed'''nth coll, n, not-found)
                (nil? coll)
                    not-found
                (neg? n)
                    not-found
                (string? coll)
                    (let-when [#_"String" s coll] (< n (String''length s)) => not-found
                        (Character'valueOf (String''charAt s, n))
                    )
                (array? coll)
                    (when (< n (Array'getLength coll)) => not-found
                        (Array'get coll, n)
                    )
                (matcher? coll)
                    (let-when [#_"Matcher" m coll] (< n (Matcher''groupCount m)) => not-found
                        (Matcher''group m, n)
                    )
                (map-entry? coll)
                    (let [#_"pair" e coll]
                        (case! n 0 (key e) 1 (val e) not-found)
                    )
                (sequential? coll)
                    (loop-when [#_"int" i 0 #_"seq" s (seq coll)] (and (<= i n) (some? s)) => not-found
                        (recur-when (< i n) [(inc i) (next s)] => (first s))
                    )
                :else
                    (throw! (str "nth not supported on " coll))
            )
        )
    )

(defn nth
    ([s i]           (RT'nth s i          ))
    ([s i not-found] (RT'nth s i not-found))
)

    (defn #_"IPersistentMap" RT'map [#_"Seqable" init]
        (if (empty? init) PersistentMap'EMPTY (PersistentMap'createWithCheck (anew init)))
    )

    (defn #_"IPersistentMap" RT'mapUniqueKeys [#_"Seqable" init]
        (if (empty? init) PersistentMap'EMPTY (PersistentMap'new (anew init)))
    )
)
)

(about #_"beagle.Var"

(about #_"Var"
    (defn #_"Appendable" Var'append [#_"Appendable" a, #_"Namespace" ns, #_"Symbol" sym]
        (if (some? ns)
            (-> a (Appendable''append "#'") (append (:name ns)) (Appendable''append "/") (append sym))
            (-> a (Appendable''append "#_var nil #_\"") (append sym) (Appendable''append "\""))
        )
    )
)

(about #_"Unbound"
    (defq Unbound [#_"Namespace" ns, #_"Symbol" sym])

    #_inherit
    (defm Unbound AFn)

    (defn #_"Unbound" Unbound'new [#_"Namespace" ns, #_"Symbol" sym]
        (new* Unbound'class (anew [ns, sym]))
    )

    (defn #_"Appendable" Unbound''append [#_"Unbound" this, #_"Appendable" a]
        (-> a (Appendable''append "#_unbound ") (Var'append (:ns this), (:sym this)))
    )

    (defm Unbound IObject
        (IObject'''equals => identical?)
    )

    (defm Unbound IAppend
        (IAppend'''append => Unbound''append)
    )
)

(about #_"Var"
    (declare Var''get)

    (defq Var [#_"Namespace" ns, #_"Symbol" sym, #_"Object'" root]
        java.util.concurrent.Future (get [_] (Var''get _))
    )

    (defn #_"Var" Var'new
        ([#_"Namespace" ns, #_"Symbol" sym] (Var'new ns, sym, (Unbound'new ns, sym)))
        ([#_"Namespace" ns, #_"Symbol" sym, #_"Object" root]
            (new* Var'class (anew [ns, sym, (atom root)]))
        )
    )

    (defn #_"meta" Var''meta [#_"Var" this]
        (meta (:root this))
    )

    (defn #_"meta" Var''alterMeta [#_"Var" this, #_"fn" f, #_"seq" args]
        (apply alter-meta! (:root this) f args)
    )

    (defn #_"meta" Var''resetMeta [#_"Var" this, #_"meta" m]
        (reset-meta! (:root this) m)
    )

    (defn #_"Appendable" Var''append [#_"Var" this, #_"Appendable" a]
        (Var'append a, (:ns this), (:sym this))
    )

    (defn #_"boolean" Var''hasRoot [#_"Var" this]
        (when-not (clojure-var? this) => (Var''-hasRoot this)
            (not (satisfies? Unbound @(:root this)))
        )
    )

    (defn #_"boolean" Var''isBound [#_"Var" this]
        (when-not (clojure-var? this) => (Var''-isBound this)
            (Var''hasRoot this)
        )
    )

    (defn #_"Object" Var''get [#_"Var" this]
        (when-not (clojure-var? this) => (Var''-get this)
            @(:root this)
        )
    )

(defn var-get [#_"var" x] (Var''get x))

    (defn #_"void" Var''setMacro [#_"Var" this]
        (alter-meta! this assoc :macro true)
        nil
    )

    (defn #_"boolean" Var''isMacro [#_"Var" this]
        (boolean (:macro (meta this)))
    )

    (defn #_"void" Var''bindRoot [#_"Var" this, #_"Object" root]
        (alter-meta! this dissoc :macro)
        (reset! (:root this) root)
        nil
    )

    (defn #_"Object" Var''alterRoot [#_"Var" this, #_"fn" f, #_"seq" args]
        (when-not (clojure-var? this) => (Var''-alterRoot this, f, args)
            (apply swap! (:root this) f args)
        )
    )

    (declare Namespace''intern)

    (defn #_"Var" Var'intern
        ([#_"Namespace" ns, #_"Symbol" sym]
            (Namespace''intern ns, sym)
        )
        ([#_"Namespace" ns, #_"Symbol" sym, #_"Object" root]
            (let [#_"Var" v (Namespace''intern ns, sym)]
                (Var''bindRoot v, root)
                v
            )
        )
    )

(declare the-ns)

(defn intern
    ([ns name]
        (let [v (Var'intern (the-ns ns), name)]
            (when-some [m (meta name)]
                (reset-meta! v m)
            )
            v
        )
    )
    ([ns name root]
        (let [v (Var'intern (the-ns ns), name, root)]
            (when-some [m (meta name)]
                (reset-meta! v m)
            )
            v
        )
    )
)

    (defn #_"Object" Var''invoke
        ([#_"Var" this]                                                   (IFn'''invoke @this))
        ([#_"Var" this, a1]                                               (IFn'''invoke @this, a1))
        ([#_"Var" this, a1, a2]                                           (IFn'''invoke @this, a1, a2))
        ([#_"Var" this, a1, a2, a3]                                       (IFn'''invoke @this, a1, a2, a3))
        ([#_"Var" this, a1, a2, a3, a4]                                   (IFn'''invoke @this, a1, a2, a3, a4))
        ([#_"Var" this, a1, a2, a3, a4, a5]                               (IFn'''invoke @this, a1, a2, a3, a4, a5))
        ([#_"Var" this, a1, a2, a3, a4, a5, a6]                           (IFn'''invoke @this, a1, a2, a3, a4, a5, a6))
        ([#_"Var" this, a1, a2, a3, a4, a5, a6, a7]                       (IFn'''invoke @this, a1, a2, a3, a4, a5, a6, a7))
        ([#_"Var" this, a1, a2, a3, a4, a5, a6, a7, a8]                   (IFn'''invoke @this, a1, a2, a3, a4, a5, a6, a7, a8))
        ([#_"Var" this, a1, a2, a3, a4, a5, a6, a7, a8, a9]               (IFn'''invoke @this, a1, a2, a3, a4, a5, a6, a7, a8, a9))
        ([#_"Var" this, a1, a2, a3, a4, a5, a6, a7, a8, a9, #_"seq" args] (IFn'''invoke @this, a1, a2, a3, a4, a5, a6, a7, a8, a9, args))
    )

    (defn #_"Object" Var''applyTo [#_"Var" this, #_"seq" args]
        (IFn'''applyTo @this, args)
    )

    (defm Var IMeta
        (IMeta'''meta => Var''meta)
    )

    (defm Var IReference
        (IReference'''alterMeta => Var''alterMeta)
        (IReference'''resetMeta => Var''resetMeta)
    )

    (defm Var IObject
        (IObject'''equals => identical?)
    )

    (defm Var IAppend
        (IAppend'''append => Var''append)
    )

    (defm Var IDeref
        (IDeref'''deref => Var''get)
    )

    (defm Var IFn
        (IFn'''invoke => Var''invoke)
        (IFn'''applyTo => Var''applyTo)
    )
)

(defn alter-var-root [#_"var" v f & args] (Var''alterRoot v f args))

(defn bound? [& vars] (every? #(Var''isBound #_"var" %) vars))

(defmacro defonce [name expr]
    `(let-when [v# (def ~name)] (not (Var''hasRoot v#))
        (def ~name ~expr)
    )
)
)

(about #_"beagle.Namespace"

(about #_"Namespace"
    (defq Namespace [#_"Symbol" name, #_"{Symbol Var}'" mappings, #_"{Symbol Namespace}'" aliases])

    (def #_"{Symbol Namespace}'" Namespace'namespaces (atom (array-map)))

    (defn #_"Namespace" Namespace'find [#_"Symbol" name]
        (get @Namespace'namespaces name)
    )

(defn find-ns [sym] (Namespace'find sym))

(defn #_"Namespace" the-ns [x]
    (when-not (clojure-namespace? x) => x
        (if (satisfies? Namespace x)
            x
            (or (find-ns x) (throw! (str "no namespace: " x " found")))
        )
    )
)

    (defn #_"Namespace" Namespace'new [#_"Symbol" name]
        (new* Namespace'class (anew [name, (atom (array-map)), (atom (array-map))]))
    )

    (defn #_"Namespace" Namespace'findOrCreate [#_"Symbol" name]
        (or (Namespace'find name)
            (let [#_"Namespace" ns (Namespace'new name)]
                (swap! Namespace'namespaces assoc name ns)
                ns
            )
        )
    )

(defn create-ns [sym] (Namespace'findOrCreate sym))

    (defn #_"Appendable" Namespace''append [#_"Namespace" this, #_"Appendable" a]
        (Appendable''append a, (:name (:name this)))
    )

(defn ns-name [ns] (:name (the-ns ns)))

    (defn #_"map" Namespace''getMappings [#_"Namespace" this]
        (when-not (clojure-namespace? this) => (Namespace''-getMappings this)
            @(:mappings this)
        )
    )

(defn ns-map [ns] (Namespace''getMappings (the-ns ns)))

    (defn #_"Object" Namespace''getMapping [#_"Namespace" this, #_"Symbol" name]
        (when-not (clojure-namespace? this) => (Namespace''-getMapping this, name)
            (get @(:mappings this) name)
        )
    )

(defn filter-key [f f? m]
    (loop-when-recur [s (seq m) m (array-map)] s [(next s) (let [e (first s)] (if (f? (f e)) (assoc m (key e) (val e)) m))] => m)
)

(defn ns-interns [ns]
    (let [ns (the-ns ns)]
        (filter-key val (fn [#_"var" v] (and (var? v) (= ns (:ns v)))) (ns-map ns))
    )
)

    (defn #_"void" Namespace''warnOrFailOnReplace [#_"Namespace" this, #_"Symbol" sym, #_"Object" o, #_"var" var]
        (or
            (when (var? o)
                (when (= (:ns o) this) => (throw! (str sym " already refers to: " o " in namespace: " (:name this)))
                    :ok
                )
            )
            (PrintWriter''println -/*err*, (str "WARNING: " sym " already refers to: " o " in namespace: " (:name this) ", being replaced by: " var))
        )
        nil
    )

    (defn #_"var" Namespace''intern [#_"Namespace" this, #_"Symbol" sym]
        (when-not (clojure-namespace? this) => (Namespace''-intern this, sym)
            (when (nil? (:ns sym)) => (throw! "can't intern namespace-qualified symbol")
                (let [#_"Object" o
                        (or (get @(:mappings this) sym)
                            (let [#_"var" v (Var'new this, sym)]
                                (swap! (:mappings this) assoc sym v)
                                v
                            )
                        )]
                    (when-not (and (var? o) (= (:ns o) this)) => o
                        (let [#_"var" v (Var'new this, sym)]
                            (Namespace''warnOrFailOnReplace this, sym, o, v)
                            (swap! (:mappings this) assoc sym v)
                            v
                        )
                    )
                )
            )
        )
    )

    (defn #_"var" Namespace''refer [#_"Namespace" this, #_"Symbol" sym, #_"var" var]
        (when (nil? (:ns sym)) => (throw! "can't intern namespace-qualified symbol")
            (let [#_"Object" o
                    (or (get @(:mappings this) sym)
                        (do
                            (swap! (:mappings this) assoc sym var)
                            var
                        )
                    )]
                (when-not (= o var)
                    (Namespace''warnOrFailOnReplace this, sym, o, var)
                    (swap! (:mappings this) assoc sym var)
                )
                var
            )
        )
    )

(declare ^:dynamic *ns*)

(defn refer [ns-sym & filters]
    (let [ns (the-ns ns-sym) ps* (ns-interns ns) fs* (apply array-map filters)
          r (:refer fs*) s (if (= r :all) (keys ps*) (or r (:only fs*) (keys ps*)))]
        (when (sequential? s) => (throw! "the value of :only/:refer must be a sequential collection of symbols")
            (let [es* (set (:exclude fs*)) rs* (or (:rename fs*) (array-map))]
                (doseq [x (remove es* s)]
                    (when-some [v (ps* x)] => (throw! (str x (if (get (ns-interns ns) x) " is not public" " does not exist")))
                        (Namespace''refer *ns* (or (rs* x) x) v)
                    )
                )
            )
        )
    )
)

    (defn #_"var" Namespace''findInternedVar [#_"Namespace" this, #_"Symbol" name]
        (when-not (clojure-namespace? this) => (Namespace''-findInternedVar this, (-/symbol (str name)))
            (let [#_"Object" o (get @(:mappings this) name)]
                (when (and (var? o) (= (:ns o) this))
                    o
                )
            )
        )
    )

    (defn #_"Namespace" Namespace''getAlias [#_"Namespace" this, #_"Symbol" alias]
        (get @(:aliases this) alias)
    )

    (defn #_"void" Namespace''addAlias [#_"Namespace" this, #_"Symbol" alias, #_"Namespace" ns]
        (when (and (some? alias) (some? ns)) => (throw! "expecting Symbol + Namespace")
            (let [#_"Object" o
                    (or (get @(:aliases this) alias)
                        (do
                            (swap! (:aliases this) assoc alias ns)
                            ns
                        )
                    )]
                (when-not (= o ns)
                    (throw! (str "alias " alias " already exists in namespace " (:name this) ", aliasing " o))
                )
            )
        )
        nil
    )

(defn alias [sym ns]
    (Namespace''addAlias *ns* sym (the-ns ns))
)

    (defm Namespace IObject
        (IObject'''equals => identical?)
    )

    (defm Namespace IAppend
        (IAppend'''append => Namespace''append)
    )
)
)

(about #_"cloiure.core"

(defn destructure [bindings]
    (letfn [(vec- [v x y]
                (let [v' (gensym "v__") s' (gensym "s__") f' (gensym "f__") amp (some #{'&} x)]
                    (loop-when [v (let [v (conj v v' y)] (if amp (conj v s' `(seq ~v')) v)) n 0 s (seq x) amp? false] s => v
                        (case! (first s)
                            '&  (recur (destructure- v (second s) s') n (next (next s)) true)
                            :as (destructure- v (second s) v')
                                (when-not amp? => (throw! "unsupported binding form, only :as can follow & parameter")
                                    (recur
                                        (destructure- (if amp (conj v f' `(first ~s') s' `(next ~s')) v)
                                            (first s)
                                            (if amp f' `(nth ~v' ~n nil))
                                        )
                                        (inc n) (next s) amp?
                                    )
                                )
                        )
                    )
                )
            )
            (map- [v x y]
                (let [m' (gensym "m__") as (:as x) or* (:or x)
                      v (conj v m' y m' `(if (seq? ~m') (apply array-map ~m') ~m')) v (if as (conj v as m') v)
                      s (reduce
                            (fn [m e] (reduce #(assoc %1 %2 ((val e) %2)) (dissoc m (key e)) ((key e) m)))
                            (dissoc x :as :or)
                            (reduce
                                (fn [m k]
                                    (when (keyword? k) => m
                                        (let [ns (namespace k)]
                                            (case! (name k)
                                                "keys" (assoc m k #(keyword (or ns (namespace %)) (name %)))
                                                "syms" (assoc m k #(list 'quote (symbol (or ns (namespace %)) (name %))))
                                                "strs" (assoc m k str)
                                                       m
                                            )
                                        )
                                    )
                                )
                                (array-map) (keys x)
                            )
                        )]
                    (loop-when [v v s (seq s)] s => v
                        (let [x (key (first s)) k (val (first s))
                              local (if (satisfies? INamed x) (with-meta (symbol nil (name x)) (meta x)) x)
                              y (if (contains? or* local)
                                    `(get ~m' ~k ~(or* local))
                                    `(get ~m' ~k)
                                )]
                            (recur (if (or (symbol? x) (keyword? x)) (conj v local y) (destructure- v x y)) (next s))
                        )
                    )
                )
            )
            (destructure- [v x y]
                (cond
                    (symbol? x) (conj v x y)
                    (vector? x) (vec- v x y)
                    (map? x)    (map- v x y)
                    :else       (throw! (str "unsupported binding form: " x))
                )
            )]
        (let [pairs (partition 2 bindings)]
            (if (every? symbol? (map first pairs))
                bindings
                (reduce #(destructure- %1 (first %2) (second %2)) (vector) pairs)
            )
        )
    )
)

#_oops!
(defmacro let [bindings & body]
    `(let* ~(destructure bindings) ~@body)
)

(defn maybe-destructured [pars body]
    (if (every? symbol? pars)
        (cons (vec pars) body)
        (loop-when [s (seq pars) pars (with-meta (vector) (meta pars)) lets (vector)] s => `(~pars (let ~lets ~@body))
            (if (symbol? (first s))
                (recur (next s) (conj pars (first s)) lets)
                (let [p' (gensym "p__")]
                    (recur (next s) (conj pars p') (conj lets (first s) p'))
                )
            )
        )
    )
)

#_oops!
(defmacro fn [& s]
    (let [name (when (symbol? (first s)) (first s)) s (if name (next s) s)
          s (if (vector? (first s))
                (list s)
                (if (seq? (first s))
                    s
                    (throw!
                        (if (seq s)
                            (str "parameter declaration " (first s) " should be a vector")
                            (str "parameter declaration missing")
                        )
                    )
                )
            )
          sig-
            (fn* [sig]
                (when (seq? sig) => (throw! (str "invalid signature " sig " should be a list"))
                    (let-when [[pars & body] sig] (vector? pars) => (throw!
                                                                        (if (seq? (first s))
                                                                            (str "parameter declaration " pars " should be a vector")
                                                                            (str "invalid signature " sig " should be a list")
                                                                        )
                                                                    )
                        (maybe-destructured pars (or (and (map? (first body)) (next body)) body))
                    )
                )
            )
          s (map sig- s)]
        (with-meta (if name (list* 'fn* name s) (cons 'fn* s)) (meta &form))
    )
)

#_oops!
(defmacro loop [bindings & body]
    (if (= (destructure bindings) bindings)
        `(loop* ~bindings ~@body)
        (let [s (take-nth 2 bindings) s' (map #(if (symbol? %) % (gensym)) s)
              v (reduce
                    (fn [v [x y z]] (if (symbol? x) (conj v z y) (conj v z y x z)))
                    (vector) (map vector s (take-nth 2 (drop 1 bindings)) s')
                )]
            `(let ~v
                (loop* ~(vec (interleave s' s'))
                    (let ~(vec (interleave s s'))
                        ~@body
                    )
                )
            )
        )
    )
)

(about #_"def{n,macro}"
    #_oops!
    (defmacro defn [fname & s]
        (when (symbol? fname) => (throw! "first argument to defn must be a symbol")
            (let [m (if (map?    (first s)) (first s) (array-map))
                  s (if (map?    (first s)) (next s)   s)
                  s (if (vector? (first s)) (list s)   s)
                  m (conj (or (meta fname) (array-map)) m)]
                (list 'def (with-meta fname m) (cons `fn s))
            )
        )
    )

    #_oops!
    (defmacro defmacro [name & args]
        (let [[m s] (split-with map? args) s (if (vector? (first s)) (list s) s)
              s (map (fn [[bindings & body]] (cons (apply vector '&form '&env bindings) body)) s)]
            `(do (defn ~name ~@m ~@s) (Var''setMacro (var ~name)) (var ~name))
        )
    )
)

#_oops!
(defmacro for [bindings body]
    (letfn [(group- [bindings]
                (reduce
                    (fn [v [x y]]
                        (if (keyword? x)
                            (conj (pop v) (conj (peek v) [x y]))
                            (conj v [x y])
                        )
                    )
                    (vector) (partition 2 bindings)
                )
            )
            (emit- [[[x _ & z] & [[_ e] :as more]]]
                (let [f' (gensym "f__") s' (gensym "s__")]
                    (letfn [(mod- [[[k v] & z]]
                                (if (keyword? k)
                                    (case! k
                                        :let   `(let ~v ~(mod- z))
                                        :while `(when ~v ~(mod- z))
                                        :when  `(if ~v ~(mod- z) (recur (next ~s')))
                                    )
                                    (when more => `(cons ~body (~f' (next ~s')))
                                        `(let [f# ~(emit- more) s# (seq (f# ~e))]
                                            (if s#
                                                (concat s# (~f' (next ~s')))
                                                (recur (next ~s'))
                                            )
                                        )
                                    )
                                )
                            )]
                        (if more
                            #_"not the inner-most loop"
                            `(fn ~f' [~s']
                                (lazy-seq
                                    (loop [~s' ~s']
                                        (when-first [~x ~s']
                                            ~(mod- z)
                                        )
                                    )
                                )
                            )
                            #_"inner-most loop"
                            `(fn ~f' [~s']
                                (lazy-seq
                                    (loop [~s' ~s']
                                        (when-some [~s' (seq ~s')]
                                            (let [~x (first ~s')]
                                                ~(mod- z)
                                            )
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )]
        `(~(emit- (group- bindings)) ~(second bindings))
    )
)

(defn memoize [f]
    (let [mem (atom (array-map))]
        (fn [& args]
            (if-some [e (find @mem args)]
                (val e)
                (let [r (apply f args)]
                    (swap! mem assoc args r)
                    r
                )
            )
        )
    )
)
)

(about #_"beagle.Compiler"
    (defp Expr
        (#_"gen" Expr'''emit [#_"Expr" this, #_"Context" context, #_"map" scope, #_"gen" gen])
    )

    (defp Recur)

    (defp LiteralExpr)
    (defp UnresolvedVarExpr)
    (defp VarExpr)
    (defp TheVarExpr)
    (defp BodyExpr)
    (defp MetaExpr)
    (defp IfExpr)
    (defp MapExpr)
    (defp SetExpr)
    (defp VectorExpr)
    (defp InvokeExpr)
    (defp LocalBinding)
    (defp LocalBindingExpr)
    (defp FnMethod)
    (defp FnExpr)
    (defp DefExpr)
    (defp LetFnExpr)
    (defp LetExpr)
    (defp RecurExpr)
    (defp ThrowExpr)
)

(about #_"beagle.Machine"

(about #_"Machine"
    (defn #_"Object" Machine'compute [#_"code" code, #_"array" vars]
        (loop [#_"stack" s nil #_"int" i 0]
            (let [[x y] (nth code i)]
                (case! x
                    :anew     (let [[    a & s] s]                             (recur (cons (anew a) s)           (inc i)))
                    :apply    (let [[  b a & s] s]                             (recur (cons (apply a b) s)        (inc i)))
                    :aset     (let [[c b a & s] s] (aset! a b c)               (recur s                           (inc i)))
                    :create   (let [[    a & s] s]                             (recur (cons (Closure'new y, a) s) (inc i)))
                    :dup      (let [[    a]     s]                             (recur (cons a s)                  (inc i)))
                    :get      (let [[    a & s] s]                             (recur (cons (get @(:_env a) y) s) (inc i)))
                    :goto                                                      (recur s                        @y)
                    :if-eq?   (let [[  b a & s] s]                             (recur s        (if     (= a b) @y (inc i))))
                    :if-nil?  (let [[    a & s] s]                             (recur s        (if  (nil? a)   @y (inc i))))
                    :invoke-1 (let [[    a & s] s]                             (recur (cons (y a) s)              (inc i)))
                    :invoke-2 (let [[  b a & s] s]                             (recur (cons (y a b) s)            (inc i)))
                    :load                                                      (recur (cons (aget vars y) s)      (inc i))
                    :pop                                                       (recur (next s)                    (inc i))
                    :push                                                      (recur (cons y s)                  (inc i))
                    :put      (let [[  b a & s] s] (swap! (:_env a) assoc y b) (recur s                           (inc i)))
                    :return                        (first s)
                    :store    (let [[    a & s] s] (aset! vars y a)            (recur s                           (inc i)))
                    :throw                         (throw (first s))
                )
            )
        )
    )
)
)

(about #_"beagle.Compiler"

(about #_"asm"
    (defn #_"gen" Gen'new [] (vector))

    (defn #_"label" Gen''label [#_"gen" gen] (atom nil))

    (defn Gen''mark
        (#_"label" [#_"gen" gen] (atom (count gen)))
        (#_"gen" [#_"gen" gen, #_"label" label] (reset! label (count gen)) gen)
    )

    (defn #_"gen" Gen''anew    [#_"gen" gen]                          (conj gen [:anew]))
    (defn #_"gen" Gen''apply   [#_"gen" gen]                          (conj gen [:apply]))
    (defn #_"gen" Gen''aset    [#_"gen" gen]                          (conj gen [:aset]))
    (defn #_"gen" Gen''create  [#_"gen" gen, #_"FnExpr" fun]          (conj gen [:create fun]))
    (defn #_"gen" Gen''dup     [#_"gen" gen]                          (conj gen [:dup]))
    (defn #_"gen" Gen''get     [#_"gen" gen, #_"Symbol" name]         (conj gen [:get name]))
    (defn #_"gen" Gen''goto    [#_"gen" gen, #_"label" label]         (conj gen [:goto label]))
    (defn #_"gen" Gen''if-eq?  [#_"gen" gen, #_"label" label]         (conj gen [:if-eq? label]))
    (defn #_"gen" Gen''if-nil? [#_"gen" gen, #_"label" label]         (conj gen [:if-nil? label]))
    (defn #_"gen" Gen''invoke  [#_"gen" gen, #_"fn" f, #_"int" arity] (conj gen [(-/keyword (str "invoke" \- arity)) f]))
    (defn #_"gen" Gen''load    [#_"gen" gen, #_"int" index]           (conj gen [:load index]))
    (defn #_"gen" Gen''pop     [#_"gen" gen]                          (conj gen [:pop]))
    (defn #_"gen" Gen''push    [#_"gen" gen, #_"value" value]         (conj gen [:push value]))
    (defn #_"gen" Gen''put     [#_"gen" gen, #_"Symbol" name]         (conj gen [:put name]))
    (defn #_"gen" Gen''return  [#_"gen" gen]                          (conj gen [:return]))
    (defn #_"gen" Gen''store   [#_"gen" gen, #_"int" index]           (conj gen [:store index]))
    (defn #_"gen" Gen''throw   [#_"gen" gen]                          (conj gen [:throw]))
)

(about #_"Compiler"
    (def #_"int" Compiler'MAX_POSITIONAL_ARITY #_9 (+ 9 2))

    (defn #_"Namespace" Compiler'namespaceFor
        ([#_"Symbol" sym] (Compiler'namespaceFor *ns*, sym))
        ([#_"Namespace" inns, #_"Symbol" sym]
            (let [#_"Symbol" nsSym (symbol (:ns sym))]
                (or (Namespace''getAlias inns, nsSym) (find-ns nsSym))
            )
        )
    )

    (defn #_"Symbol" Compiler'resolveSymbol [#_"Symbol" sym]
        (cond
            (pos? (String''indexOf (:name sym), (int \.)))
                sym
            (some? (:ns sym))
                (let [#_"Namespace" ns (Compiler'namespaceFor sym)]
                    (if (clojure-namespace? ns)
                        (if (and (some? ns) (not (and (some? (-/name (-/ns-name ns))) (= (-/name (-/ns-name ns)) (-/namespace sym)))))
                            (symbol (-/name (-/ns-name ns)) (-/name sym))
                            sym
                        )
                        (if (and (some? ns) (not (and (some? (:name (:name ns))) (= (:name (:name ns)) (:ns sym)))))
                            (symbol (:name (:name ns)) (:name sym))
                            sym
                        )
                    )
                )
            :else
                (let [#_"Object" o (Namespace''getMapping *ns*, sym)]
                    (cond
                        (nil? o) (symbol (:name (:name *ns*)) (:name sym))
                        (var? o) (symbol (:name (:name (:ns o))) (:name (:sym o)))
                    )
                )
        )
    )

    (defn #_"Var" Compiler'lookupVar [#_"Symbol" sym, #_"boolean" intern?]
        (let [sym (symbol! sym)]
            (cond
                (some? (:ns sym))
                    (when-some [#_"Namespace" ns (Compiler'namespaceFor sym)]
                        (let [#_"Symbol" name (symbol (:name sym))]
                            (if (and intern? (= ns *ns*))
                                (Namespace''intern ns, name)
                                (Namespace''findInternedVar ns, name)
                            )
                        )
                    )
                :else
                    (let [#_"Object" o (Namespace''getMapping *ns*, sym)]
                        (cond
                            (nil? o)
                                (when intern?
                                    (Namespace''intern *ns*, (symbol (:name sym)))
                                )
                            (var? o)
                                o
                            :else
                                (throw! (str "expecting var, but " sym " is mapped to " o))
                        )
                    )
            )
        )
    )

    (defn #_"Var" Compiler'maybeMacro [#_"Object" op, #_"map" scope]
        (when-not (and (symbol? op) (some? (get @(get scope :'local-env) op)))
            (when (or (symbol? op) (var? op))
                (let [#_"Var" v (if (var? op) op (Compiler'lookupVar op, false))]
                    (when (and (some? v) (get (meta v) :macro))
                        v
                    )
                )
            )
        )
    )

    (defn #_"Object" Compiler'resolveIn [#_"Namespace" n, #_"Symbol" sym]
        (let [sym (symbol! sym)]
            (cond
                (some? (:ns sym))
                    (when-some [#_"Namespace" ns (Compiler'namespaceFor n, sym)]                     => (throw! (str "no such namespace: " (:ns sym)))
                        (when-some [#_"Var" v (Namespace''findInternedVar ns, (symbol (:name sym)))] => (throw! (str "no such var: " sym))
                            v
                        )
                    )
                :else
                    (or (Namespace''getMapping n, sym) (throw! (str "unable to resolve symbol: " sym " in this context")))
            )
        )
    )

    (defn #_"gen" Compiler'emitArgs [#_"map" scope, #_"gen" gen, #_"indexed" args]
        (let [
            gen (Gen''push gen, (count args))
            gen (Gen''anew gen)
        ]
            (loop-when [gen gen #_"int" i 0] (< i (count args)) => gen
                (let [
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (Expr'''emit (nth args i), :Context'EXPRESSION, scope, gen)
                    gen (Gen''aset gen)
                ]
                    (recur gen (inc i))
                )
            )
        )
    )

    (declare FnMethod''emitLocal)

    (defn #_"gen" Compiler'emitLocals [#_"map" scope, #_"gen" gen, #_"map" locals]
        (let [
            gen (Gen''push gen, (<< (count locals) 1))
            gen (Gen''anew gen)
        ]
            (loop-when [gen gen #_"int" i 0 #_"seq" s (vals locals)] (some? s) => gen
                (let [
                    #_"LocalBinding" lb (first s)
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (Gen''push gen, (:sym lb))
                    gen (Gen''aset gen)
                    i (inc i)
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (FnMethod''emitLocal (get scope :fm), gen, lb)
                    gen (Gen''aset gen)
                    i (inc i)
                ]
                    (recur gen i (next s))
                )
            )
        )
    )
)

(about #_"LiteralExpr"
    (defr LiteralExpr)

    (defn #_"LiteralExpr" LiteralExpr'new [#_"Object" value]
        (new* LiteralExpr'class
            (-/hash-map
                #_"Object" :value value
            )
        )
    )

    (def #_"LiteralExpr" LiteralExpr'NIL   (LiteralExpr'new nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (LiteralExpr'new true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (LiteralExpr'new false))

    (defn #_"Expr" LiteralExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (dec (count form))]
            (when (= n 1) => (throw! (str "wrong number of arguments passed to quote: " n))
                (let [#_"Object" value (second form)]
                    (case! value
                        nil                 LiteralExpr'NIL
                        true                LiteralExpr'TRUE
                        false               LiteralExpr'FALSE
                        (cond
                            (string? value) (LiteralExpr'new (String''intern value))
                            :else           (LiteralExpr'new value)
                        )
                    )
                )
            )
        )
    )

    (defn #_"gen" LiteralExpr''emit [#_"LiteralExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (when-not (= context :Context'STATEMENT) => gen
            (Gen''push gen, (:value this))
        )
    )

    (defm LiteralExpr Expr
        (Expr'''emit => LiteralExpr''emit)
    )
)

(about #_"UnresolvedVarExpr"
    (defr UnresolvedVarExpr)

    (defn #_"UnresolvedVarExpr" UnresolvedVarExpr'new [#_"Symbol" symbol]
        (new* UnresolvedVarExpr'class
            (-/hash-map
                #_"Symbol" :symbol symbol
            )
        )
    )

    (defn #_"gen" UnresolvedVarExpr''emit [#_"UnresolvedVarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        gen
    )

    (defm UnresolvedVarExpr Expr
        (Expr'''emit => UnresolvedVarExpr''emit)
    )
)

(about #_"VarExpr"
    (defr VarExpr)

    (defn #_"VarExpr" VarExpr'new [#_"Var" var]
        (new* VarExpr'class
            (-/hash-map
                #_"Var" :var var
            )
        )
    )

    (defn #_"gen" VarExpr''emit [#_"VarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (:var this))
            gen (Gen''invoke gen, var-get, 1)
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm VarExpr Expr
        (Expr'''emit => VarExpr''emit)
    )
)

(about #_"TheVarExpr"
    (defr TheVarExpr)

    (defn #_"TheVarExpr" TheVarExpr'new [#_"Var" var]
        (new* TheVarExpr'class
            (-/hash-map
                #_"Var" :var var
            )
        )
    )

    (defn #_"Expr" TheVarExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"Symbol" sym (second form) #_"Var" v (Compiler'lookupVar sym, false)]
            (when (some? v) => (throw! (str "unable to resolve var: " sym " in this context"))
                (TheVarExpr'new v)
            )
        )
    )

    (defn #_"gen" TheVarExpr''emit [#_"TheVarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (when-not (= context :Context'STATEMENT) => gen
            (Gen''push gen, (:var this))
        )
    )

    (defm TheVarExpr Expr
        (Expr'''emit => TheVarExpr''emit)
    )
)

(about #_"BodyExpr"
    (defr BodyExpr)

    (defn #_"BodyExpr" BodyExpr'new [#_"vector" exprs]
        (new* BodyExpr'class
            (-/hash-map
                #_"vector" :exprs exprs
            )
        )
    )

    (declare Compiler'analyze)

    (defn #_"Expr" BodyExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"seq" s form s (if (= (first s) 'do) (next s) s)
              #_"vector" v
                (loop-when [v (vector) s s] (some? s) => v
                    (let [#_"Context" c (if (or (= context :Context'STATEMENT) (some? (next s))) :Context'STATEMENT context)]
                        (recur (conj v (Compiler'analyze (first s), c, scope)) (next s))
                    )
                )]
            (BodyExpr'new (if (pos? (count v)) v (conj v LiteralExpr'NIL)))
        )
    )

    (defn #_"gen" BodyExpr''emit [#_"BodyExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (loop-when-recur [gen gen #_"seq" s (seq (:exprs this))]
                         (some? (next s))
                         [(Expr'''emit (first s), :Context'STATEMENT, scope, gen) (next s)]
                      => (Expr'''emit (first s), context, scope, gen)
        )
    )

    (defm BodyExpr Expr
        (Expr'''emit => BodyExpr''emit)
    )
)

(about #_"MetaExpr"
    (defr MetaExpr)

    (defn #_"MetaExpr" MetaExpr'new [#_"Expr" expr, #_"Expr" meta]
        (new* MetaExpr'class
            (-/hash-map
                #_"Expr" :expr expr
                #_"Expr" :meta meta
            )
        )
    )

    (defn #_"gen" MetaExpr''emit [#_"MetaExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Expr'''emit (:expr this), :Context'EXPRESSION, scope, gen)
            gen (Expr'''emit (:meta this), :Context'EXPRESSION, scope, gen)
            gen (Gen''invoke gen, with-meta, 2)
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm MetaExpr Expr
        (Expr'''emit => MetaExpr''emit)
    )
)

(about #_"IfExpr"
    (defr IfExpr)

    (defn #_"IfExpr" IfExpr'new [#_"Expr" test, #_"Expr" then, #_"Expr" else]
        (new* IfExpr'class
            (-/hash-map
                #_"Expr" :test test
                #_"Expr" :then then
                #_"Expr" :else else
            )
        )
    )

    (defn #_"Expr" IfExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (cond
            (< 4 (count form)) (throw! "too many arguments to if")
            (< (count form) 3) (throw! "too few arguments to if")
        )
        (let [#_"Expr" test (Compiler'analyze (second form), scope)
              #_"Expr" then (Compiler'analyze (third form), context, scope)
              #_"Expr" else (Compiler'analyze (fourth form), context, scope)]
            (IfExpr'new test, then, else)
        )
    )

    (defn #_"gen" IfExpr''emit [#_"IfExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            #_"label" l'nil (Gen''label gen) #_"label" l'false (Gen''label gen) #_"label" l'end (Gen''label gen)
            gen (Expr'''emit (:test this), :Context'EXPRESSION, scope, gen)
            gen (Gen''dup gen)
            gen (Gen''if-nil? gen, l'nil)
            gen (Gen''push gen, false)
            gen (Gen''if-eq? gen, l'false)
            gen (Expr'''emit (:then this), context, scope, gen)
            gen (Gen''goto gen, l'end)
            gen (Gen''mark gen, l'nil)
            gen (Gen''pop gen)
            gen (Gen''mark gen, l'false)
            gen (Expr'''emit (:else this), context, scope, gen)
            gen (Gen''mark gen, l'end)
        ]
            gen
        )
    )

    (defm IfExpr Expr
        (Expr'''emit => IfExpr''emit)
    )
)

(about #_"MapExpr"
    (defr MapExpr)

    (defn #_"MapExpr" MapExpr'new [#_"vector" args]
        (new* MapExpr'class
            (-/hash-map
                #_"vector" :args args
            )
        )
    )

    (defn #_"Expr" MapExpr'parse [#_"map" form, #_"map" scope]
        (let [[#_"vector" args #_"boolean" literal?]
                (loop-when [args (vector), literal? true, #_"set" keys (array-set), #_"seq" s (seq form)] (some? s) => [args literal?]
                    (let [#_"pair" e (first s) #_"Expr" k (Compiler'analyze (key e), scope) #_"Expr" v (Compiler'analyze (val e), scope)
                          [literal? keys]
                            (when (satisfies? LiteralExpr k) => [false keys]
                                (when-not (contains? keys (:value k)) => (throw! "duplicate constant keys in map")
                                    [literal? (conj keys (:value k))]
                                )
                            )]
                        (recur (conj args k v) (and literal? (satisfies? LiteralExpr v)) keys (next s))
                    )
                )
              #_"Expr" e
                (when literal? => (MapExpr'new args)
                    (LiteralExpr'new (apply array-map (map :value args)))
                )]
            (when-some [#_"meta" m (meta form)] => e
                (MetaExpr'new e, (MapExpr'parse m, scope))
            )
        )
    )

    (defn #_"gen" MapExpr''emit [#_"MapExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            #_"int" n (count (:args this))
            [#_"boolean" literal? #_"boolean" unique?]
                (loop-when [literal? true, unique? true, #_"set" keys (array-set), #_"int" i 0] (< i n) => [literal? unique?]
                    (let [#_"Expr" k (nth (:args this) i)
                          [literal? unique? keys]
                            (when (satisfies? LiteralExpr k) => [false unique? keys]
                                (when-not (contains? keys (:value k)) => [literal? false keys]
                                    [literal? unique? (conj keys (:value k))]
                                )
                            )]
                        (recur literal? unique? keys (+ i 2))
                    )
                )
            gen (Compiler'emitArgs scope, gen, (:args this))
            gen (Gen''invoke gen, (if (or (and literal? unique?) (<= n 2)) RT'mapUniqueKeys RT'map), 1)
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm MapExpr Expr
        (Expr'''emit => MapExpr''emit)
    )
)

(about #_"SetExpr"
    (defr SetExpr)

    (defn #_"SetExpr" SetExpr'new [#_"vector" args]
        (new* SetExpr'class
            (-/hash-map
                #_"vector" :args args
            )
        )
    )

    (defn #_"Expr" SetExpr'parse [#_"set" form, #_"map" scope]
        (let [[#_"vector" args #_"boolean" literal?]
                (loop-when [args (vector) literal? true #_"seq" s (seq form)] (some? s) => [args literal?]
                    (let [#_"Expr" e (Compiler'analyze (first s), scope)]
                        (recur (conj args e) (and literal? (satisfies? LiteralExpr e)) (next s))
                    )
                )
              #_"Expr" e
                (when literal? => (SetExpr'new args)
                    (LiteralExpr'new (apply array-set (map :value args)))
                )]
            (when-some [#_"meta" m (meta form)] => e
                (MetaExpr'new e, (MapExpr'parse m, scope))
            )
        )
    )

    (defn #_"gen" SetExpr''emit [#_"SetExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen
                (when (seq (:args this)) => (Gen''push gen, PersistentSet'EMPTY)
                    (let [gen (Compiler'emitArgs scope, gen, (:args this))]
                        (Gen''invoke gen, PersistentSet'createWithCheck, 1)
                    )
                )
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm SetExpr Expr
        (Expr'''emit => SetExpr''emit)
    )
)

(about #_"VectorExpr"
    (defr VectorExpr)

    (defn #_"VectorExpr" VectorExpr'new [#_"vector" args]
        (new* VectorExpr'class
            (-/hash-map
                #_"vector" :args args
            )
        )
    )

    (defn #_"Expr" VectorExpr'parse [#_"vector" form, #_"map" scope]
        (let [[#_"vector" args #_"boolean" literal?]
                (loop-when [args (vector) literal? true #_"seq" s (seq form)] (some? s) => [args literal?]
                    (let [#_"Expr" e (Compiler'analyze (first s), scope)]
                        (recur (conj args e) (and literal? (satisfies? LiteralExpr e)) (next s))
                    )
                )
              #_"Expr" e
                (when literal? => (VectorExpr'new args)
                    (LiteralExpr'new (mapv :value args))
                )]
            (when-some [#_"meta" m (meta form)] => e
                (MetaExpr'new e, (MapExpr'parse m, scope))
            )
        )
    )

    (defn #_"gen" VectorExpr''emit [#_"VectorExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen
                (when (seq (:args this)) => (Gen''push gen, PersistentVector'EMPTY)
                    (let [gen (Compiler'emitArgs scope, gen, (:args this))]
                        (Gen''invoke gen, vec, 1)
                    )
                )
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm VectorExpr Expr
        (Expr'''emit => VectorExpr''emit)
    )
)

(about #_"InvokeExpr"
    (defr InvokeExpr)

    (defn #_"InvokeExpr" InvokeExpr'new [#_"Expr" fexpr, #_"vector" args]
        (new* InvokeExpr'class
            (-/hash-map
                #_"Expr" :fexpr fexpr
                #_"vector" :args args
            )
        )
    )

    (defn #_"Expr" InvokeExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"Expr" fexpr (Compiler'analyze (first form), scope)
              #_"vector" args (mapv #(Compiler'analyze %, scope) (next form))]
            (InvokeExpr'new fexpr, args)
        )
    )

    (defn #_"gen" InvokeExpr''emit [#_"InvokeExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Expr'''emit (:fexpr this), :Context'EXPRESSION, scope, gen)
            gen (Compiler'emitArgs scope, gen, (:args this))
            gen (Gen''apply gen)
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm InvokeExpr Expr
        (Expr'''emit => InvokeExpr''emit)
    )
)

(about #_"LocalBinding"
    (defr LocalBinding)

    (defn #_"LocalBinding" LocalBinding'new [#_"Symbol" sym, #_"Expr" init, #_"int" idx]
        (new* LocalBinding'class
            (-/hash-map
                #_"int" :uid (next-id!)
                #_"Symbol" :sym sym
                #_"Expr'" :'init (atom init)
                #_"int" :idx idx
            )
        )
    )
)

(about #_"LocalBindingExpr"
    (defr LocalBindingExpr)

    (defn #_"LocalBindingExpr" LocalBindingExpr'new [#_"LocalBinding" lb]
        (new* LocalBindingExpr'class
            (-/hash-map
                #_"LocalBinding" :lb lb
            )
        )
    )

    (defn #_"gen" LocalBindingExpr''emit [#_"LocalBindingExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (when-not (= context :Context'STATEMENT) => gen
            (FnMethod''emitLocal (get scope :fm), gen, (:lb this))
        )
    )

    (defm LocalBindingExpr Expr
        (Expr'''emit => LocalBindingExpr''emit)
    )
)

(about #_"FnMethod"
    (defr FnMethod)

    (defn #_"FnMethod" FnMethod'new [#_"FnExpr" fun, #_"FnMethod" parent]
        (new* FnMethod'class
            (-/hash-map
                #_"FnExpr" :fun fun
                #_"FnMethod" :parent parent
                #_"{int LocalBinding}'" :'locals (atom (array-map))
                #_"Integer" :arity nil
                #_"Expr" :body nil
            )
        )
    )

    (defn #_"FnMethod" FnMethod'parse [#_"FnExpr" fun, #_"seq" form, #_"map" scope]
        (let [
            scope
                (-> scope
                    (update :fm (partial FnMethod'new fun))
                    (update :'local-env (comp atom deref))
                    (assoc :'local-num (atom 0))
                )
            _
                (when-some [#_"Symbol" f (:fname fun)]
                    (let [#_"LocalBinding" lb (LocalBinding'new f, nil, @(get scope :'local-num))]
                        (swap! (get scope :'local-env) assoc (:sym lb) lb)
                        (swap! (:'locals (get scope :fm)) assoc (:uid lb) lb)
                    )
                )
            [#_"[LocalBinding]" lbs #_"int" arity]
                (loop-when [lbs (vector) arity 0 #_"boolean" variadic? false #_"seq" s (seq (first form))] (some? s) => (if (and variadic? (not (neg? arity))) (throw! "missing variadic parameter") [lbs arity])
                    (let [#_"symbol?" sym (first s)]
                        (when (symbol? sym)        => (throw! "function parameters must be symbols")
                            (when (nil? (:ns sym)) => (throw! (str "can't use qualified name as parameter: " sym))
                                (cond
                                    (= sym '&)
                                        (when-not variadic? => (throw! "overkill variadic parameter list")
                                            (recur lbs arity true (next s))
                                        )
                                    (neg? arity)
                                        (throw! (str "excess variadic parameter: " sym))
                                    ((if variadic? <= <) arity Compiler'MAX_POSITIONAL_ARITY)
                                        (let [
                                            arity (if-not variadic? (inc arity) (- (inc arity)))
                                            #_"LocalBinding" lb (LocalBinding'new sym, nil, (swap! (get scope :'local-num) inc))
                                        ]
                                            (swap! (get scope :'local-env) assoc (:sym lb) lb)
                                            (swap! (:'locals (get scope :fm)) assoc (:uid lb) lb)
                                            (recur (conj lbs lb) arity variadic? (next s))
                                        )
                                    :else
                                        (throw! (str "can't specify more than " Compiler'MAX_POSITIONAL_ARITY " positional parameters"))
                                )
                            )
                        )
                    )
                )
            scope
                (-> scope
                    (assoc :loop-locals lbs)
                    (update :fm assoc :arity arity)
                )
        ]
            (assoc (get scope :fm) :body (BodyExpr'parse (next form), :Context'RETURN, scope))
        )
    )

    (defn #_"gen" FnMethod''emitLocal [#_"FnMethod" this, #_"gen" gen, #_"LocalBinding" lb]
        (if (contains? @(:'closes (:fun this)) (:uid lb))
            (let [
                gen (Gen''load gen, 0)
                gen (Gen''get gen, (:sym lb))
            ]
                gen
            )
            (Gen''load gen, (:idx lb))
        )
    )

    (defn #_"gen" FnMethod''compile [#_"FnMethod" this]
        (let [
            #_"map" scope (array-map :fm this)
            #_"gen" gen (Gen'new)
            scope (assoc scope :loop-label (Gen''mark gen))
            gen (Expr'''emit (:body this), :Context'RETURN, scope, gen)
        ]
            (Gen''return gen)
        )
    )

    (def compile-and-memoize (-/memoize FnMethod''compile))
)

(about #_"FnExpr"
    (defr FnExpr)

    (defn #_"FnExpr" FnExpr'new []
        (new* FnExpr'class
            (-/hash-map
                #_"Symbol" :fname nil
                #_"{int FnMethod}" :regulars nil
                #_"FnMethod" :variadic nil
                #_"{int LocalBinding}'" :'closes (atom (array-map))
            )
        )
    )

    (defn #_"Expr" FnExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"FnExpr" fun (FnExpr'new)
            [fun form]
                (when (symbol? (second form)) => [fun form]
                    [(assoc fun :fname (second form)) (cons (symbol! 'fn*) (next (next form)))]
                )
            form
                (when (vector? (second form)) => form
                    (list (symbol! 'fn*) (next form))
                )
            fun
                (let [
                    [#_"{int FnMethod}" regulars #_"FnMethod" variadic]
                        (loop-when [regulars (array-map) variadic nil #_"seq" s (next form)] (some? s) => [regulars variadic]
                            (let [#_"FnMethod" fm (FnMethod'parse fun, (first s), scope) #_"int" n (:arity fm)]
                                (if (neg? n)
                                    (when (nil? variadic) => (throw! "can't have more than 1 variadic overload")
                                        (recur regulars fm (next s))
                                    )
                                    (when (nil? (get regulars n)) => (throw! "can't have 2 overloads with same arity")
                                        (recur (assoc regulars n fm) variadic (next s))
                                    )
                                )
                            )
                        )
                ]
                    (when (some? variadic)
                        (loop-when-recur [#_"int" n (- (:arity variadic))] (<= n Compiler'MAX_POSITIONAL_ARITY) [(inc n)]
                            (when (some? (get regulars n))
                                (throw! "can't have fixed arity function with more params than variadic function")
                            )
                        )
                    )
                    (assoc fun :regulars regulars, :variadic variadic)
                )
        ]
            (MetaExpr'new fun, (MapExpr'parse (meta form), scope)) fun
        )
    )

    (defn #_"gen" FnExpr''emit [#_"FnExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (when-not (= context :Context'STATEMENT) => gen
            (let [
                gen (Compiler'emitLocals scope, gen, @(:'closes this))
                gen (Gen''invoke gen, RT'mapUniqueKeys, 1)
            ]
                (Gen''create gen, this)
            )
        )
    )

    (defm FnExpr Expr
        (Expr'''emit => FnExpr''emit)
    )
)

(about #_"DefExpr"
    (defr DefExpr)

    (defn #_"DefExpr" DefExpr'new [#_"Var" var, #_"Expr" init, #_"Expr" meta, #_"boolean" initProvided]
        (new* DefExpr'class
            (-/hash-map
                #_"Var" :var var
                #_"Expr" :init init
                #_"Expr" :meta meta
                #_"boolean" :initProvided initProvided
            )
        )
    )

    (defn #_"Expr" DefExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (count form)]
            (cond
                (< 3 n) (throw! "too many arguments to def")
                (< n 2) (throw! "too few arguments to def")
                :else
                    (let-when [#_"symbol?" s (second form)] (symbol? s)     => (throw! "first argument to def must be a symbol")
                        (when-some [#_"Var" v (Compiler'lookupVar s, true)] => (throw! "can't refer to qualified var that doesn't exist")
                            (let [v (when-not (= (:ns v) *ns*) => v
                                        (when (nil? (:ns s))                => (throw! "can't create defs outside of current ns")
                                            (Namespace''intern *ns*, s)
                                        )
                                    )]
                                (DefExpr'new v, (Compiler'analyze (third form), scope), (Compiler'analyze (meta s), scope), (= n 3))
                            )
                        )
                    )
            )
        )
    )

    (defn #_"boolean" DefExpr''includesExplicitMetadata [#_"DefExpr" this, #_"MapExpr" expr]
        (loop-when [#_"int" i 0] (< i (count (:keyvals expr))) => false
            (recur-when (= (:k (nth (:keyvals expr) i)) :declared) [(+ i 2)] => true)
        )
    )

    (defn #_"gen" DefExpr''emit [#_"DefExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (:var this))
            gen
                (when (some? (:meta this)) => gen
                    (let [
                        gen (Gen''dup gen)
                        gen (Expr'''emit (:meta this), :Context'EXPRESSION, scope, gen)
                        gen (Gen''invoke gen, Var''resetMeta, 2)
                    ]
                        (Gen''pop gen)
                    )
                )
            gen
                (when (:initProvided this) => gen
                    (let [
                        gen (Gen''dup gen)
                        gen (Expr'''emit (:init this), :Context'EXPRESSION, scope, gen)
                        gen (Gen''invoke gen, Var''bindRoot, 2)
                    ]
                        (Gen''pop gen)
                    )
                )
        ]
            (when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    )

    (defm DefExpr Expr
        (Expr'''emit => DefExpr''emit)
    )
)

(about #_"LetFnExpr"
    (defr LetFnExpr)

    (defn #_"LetFnExpr" LetFnExpr'new [#_"[LocalBinding]" bindings, #_"Expr" body]
        (new* LetFnExpr'class
            (-/hash-map
                #_"[LocalBinding]" :bindings bindings
                #_"Expr" :body body
            )
        )
    )

    (defn #_"Expr" LetFnExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"vector?" bindings (second form)]
            (when (vector? bindings)           => (throw! "bad binding form, expected vector")
                (when (even? (count bindings)) => (throw! "bad binding form, expected matched symbol expression pairs")
                    (let [
                        scope (update scope :'local-env (comp atom deref))
                        scope (update scope :'local-num (comp atom deref))
                        #_"[LocalBinding]" lbs
                            (loop-when [lbs (vector) #_"seq" s (seq bindings)] (some? s) => lbs
                                (let [#_"symbol?" sym (first s)]
                                    (when (symbol? sym)        => (throw! (str "bad binding form, expected symbol, got: " sym))
                                        (when (nil? (:ns sym)) => (throw! (str "can't let qualified name: " sym))
                                            (let [
                                                #_"LocalBinding" lb (LocalBinding'new sym, nil, (swap! (get scope :'local-num) inc))
                                            ]
                                                (swap! (get scope :'local-env) assoc (:sym lb) lb)
                                                (swap! (:'locals (get scope :fm)) assoc (:uid lb) lb)
                                                (recur (conj lbs lb) (next (next s)))
                                            )
                                        )
                                    )
                                )
                            )
                        _
                            (loop-when-recur [#_"int" i 0] (< i (count bindings)) [(+ i 2)]
                                (reset! (:'init (nth lbs (>> i 1))) (Compiler'analyze (nth bindings (inc i)), scope))
                            )
                    ]
                        (LetFnExpr'new lbs, (BodyExpr'parse (next (next form)), context, scope))
                    )
                )
            )
        )
    )

    (defn #_"gen" LetFnExpr''emit [#_"LetFnExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen
                (loop-when [gen gen #_"seq" s (seq (:bindings this))] (some? s) => gen
                    (let [
                        #_"LocalBinding" lb (first s)
                        gen (Gen''push gen, nil)
                        gen (Gen''store gen, (:idx lb))
                    ]
                        (recur gen (next s))
                    )
                )
            [#_"{int}" lbset gen]
                (loop-when [lbset (array-set) gen gen #_"seq" s (seq (:bindings this))] (some? s) => [lbset gen]
                    (let [
                        #_"LocalBinding" lb (first s)
                        gen (Expr'''emit @(:'init lb), :Context'EXPRESSION, scope, gen)
                        gen (Gen''store gen, (:idx lb))
                    ]
                        (recur (conj lbset (:uid lb)) gen (next s))
                    )
                )
            gen
                (loop-when [gen gen #_"seq" s (seq (:bindings this))] (some? s) => gen
                    (let [
                        #_"LocalBinding" lb (first s)
                        gen (Gen''load gen, (:idx lb))
                        gen
                            (loop-when [gen gen #_"seq" s (vals @(:'closes @(:'init lb)))] (some? s) => gen
                                (let [
                                    gen
                                        (let-when [#_"LocalBinding" lb (first s)] (contains? lbset (:uid lb)) => gen
                                            (let [
                                                gen (Gen''dup gen)
                                                gen (FnMethod''emitLocal (get scope :fm), gen, lb)
                                                gen (Gen''put gen, (:sym lb))
                                            ]
                                                gen
                                            )
                                        )
                                ]
                                    (recur gen (next s))
                                )
                            )
                        gen (Gen''pop gen)
                    ]
                        (recur gen (next s))
                    )
                )
        ]
            (Expr'''emit (:body this), context, scope, gen)
        )
    )

    (defm LetFnExpr Expr
        (Expr'''emit => LetFnExpr''emit)
    )
)

(about #_"LetExpr"
    (defr LetExpr)

    (defn #_"LetExpr" LetExpr'new [#_"[LocalBinding]" bindings, #_"Expr" body, #_"boolean" loop?]
        (new* LetExpr'class
            (-/hash-map
                #_"[LocalBinding]" :bindings bindings
                #_"Expr" :body body
                #_"boolean" :loop? loop?
            )
        )
    )

    (defn #_"Expr" LetExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"vector?" bindings (second form)]
            (when (vector? bindings)           => (throw! "bad binding form, expected vector")
                (when (even? (count bindings)) => (throw! "bad binding form, expected matched symbol expression pairs")
                    (let [
                        scope (update scope :'local-env (comp atom deref))
                        scope (update scope :'local-num (comp atom deref))
                        #_"boolean" loop? (= (first form) 'loop*)
                        scope
                            (when loop? => scope
                                (dissoc scope :loop-locals)
                            )
                        #_"[LocalBinding]" lbs
                            (loop-when [lbs (vector) #_"seq" s (seq bindings)] (some? s) => lbs
                                (let [#_"symbol?" sym (first s)]
                                    (when (symbol? sym)        => (throw! (str "bad binding form, expected symbol, got: " sym))
                                        (when (nil? (:ns sym)) => (throw! (str "can't let qualified name: " sym))
                                            (let [
                                                #_"Expr" init (Compiler'analyze (second s), scope)
                                                #_"LocalBinding" lb (LocalBinding'new sym, init, (swap! (get scope :'local-num) inc))
                                            ]
                                                (swap! (get scope :'local-env) assoc (:sym lb) lb)
                                                (swap! (:'locals (get scope :fm)) assoc (:uid lb) lb)
                                                (recur (conj lbs lb) (next (next s)))
                                            )
                                        )
                                    )
                                )
                            )
                        scope
                            (when loop? => scope
                                (assoc scope :loop-locals lbs)
                            )
                        #_"Expr" body (BodyExpr'parse (next (next form)), (if loop? :Context'RETURN context), scope)
                    ]
                        (LetExpr'new lbs, body, loop?)
                    )
                )
            )
        )
    )

    (defn #_"gen" LetExpr''emit [#_"LetExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen
                (loop-when [gen gen #_"seq" s (seq (:bindings this))] (some? s) => gen
                    (let [
                        #_"LocalBinding" lb (first s)
                        gen (Expr'''emit @(:'init lb), :Context'EXPRESSION, scope, gen)
                        gen (Gen''store gen, (:idx lb))
                    ]
                        (recur gen (next s))
                    )
                )
            scope
                (when (:loop? this) => scope
                    (assoc scope :loop-label (Gen''mark gen))
                )
        ]
            (Expr'''emit (:body this), context, scope, gen)
        )
    )

    (defm LetExpr Expr
        (Expr'''emit => LetExpr''emit)
    )
)

(about #_"RecurExpr"
    (defr RecurExpr)

    (defn #_"RecurExpr" RecurExpr'new [#_"vector" loopLocals, #_"vector" args]
        (new* RecurExpr'class
            (-/hash-map
                #_"vector" :loopLocals loopLocals
                #_"vector" :args args
            )
        )
    )

    (defn #_"Expr" RecurExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (when (and (= context :Context'RETURN) (some? (get scope :loop-locals))) => (throw! "can only recur from tail position")
            (let [#_"vector" args (mapv #(Compiler'analyze %, scope) (next form)) #_"int" n (count args) #_"int" m (count (get scope :loop-locals))]
                (when (= n m) => (throw! (str "mismatched argument count to recur, expected: " m " args, got: " n))
                    (RecurExpr'new (get scope :loop-locals), args)
                )
            )
        )
    )

    (defn #_"gen" RecurExpr''emit [#_"RecurExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (when-some [#_"label" l'loop (get scope :loop-label)] => (throw! "recur misses loop label")
            (let [
                gen
                    (loop-when-recur [gen gen #_"seq" s (seq (:args this))]
                                     (some? s)
                                     [(Expr'''emit (first s), :Context'EXPRESSION, scope, gen) (next s)]
                                  => gen
                    )
                gen
                    (loop-when-recur [gen gen #_"seq" s (rseq (:loopLocals this))]
                                     (some? s)
                                     [(Gen''store gen, (:idx (first s))) (next s)]
                                  => gen
                    )
            ]
                (Gen''goto gen, l'loop)
            )
        )
    )

    (defm RecurExpr Expr
        (Expr'''emit => RecurExpr''emit)
    )
)

(about #_"ThrowExpr"
    (defr ThrowExpr)

    (defn #_"ThrowExpr" ThrowExpr'new [#_"Expr" throwable]
        (new* ThrowExpr'class
            (-/hash-map
                #_"Expr" :throwable throwable
            )
        )
    )

    (defn #_"Expr" ThrowExpr'parse [#_"seq" form, #_"Context" context, #_"map" scope]
        (cond
            (= (count form) 1) (throw! "too few arguments to throw: single Throwable expected")
            (< 2 (count form)) (throw! "too many arguments to throw: single Throwable expected")
            :else              (ThrowExpr'new (Compiler'analyze (second form), scope))
        )
    )

    (defn #_"gen" ThrowExpr''emit [#_"ThrowExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Expr'''emit (:throwable this), :Context'EXPRESSION, scope, gen)
            gen (Gen''throw gen)
        ]
            gen
        )
    )

    (defm ThrowExpr Expr
        (Expr'''emit => ThrowExpr''emit)
    )
)

(about #_"Compiler"
    (def #_"map" Compiler'specials
        (let [
            #_"map" m
                (array-map
                    '&             nil
                    'def           DefExpr'parse
                    'do            BodyExpr'parse
                    'fn*           FnExpr'parse
                    'if            IfExpr'parse
                    'let*          LetExpr'parse
                    'letfn*        LetFnExpr'parse
                    'loop*         LetExpr'parse
                    'quote         LiteralExpr'parse
                    'recur         RecurExpr'parse
                    'throw         ThrowExpr'parse
                    'var           TheVarExpr'parse
                )
        ]
            (into (#_empty identity m) (map (fn [[s f]] [(symbol! s) f]) m))
        )
    )

    (defn #_"boolean" Compiler'isSpecial [#_"Object" sym]
        (contains? Compiler'specials sym)
    )

(defn special-symbol? [s] (Compiler'isSpecial s))

    (defn #_"edn" Compiler'macroexpand1
        ([#_"edn" form] (Compiler'macroexpand1 form, nil))
        ([#_"edn" form, #_"map" scope]
            (when (seq? form) => form
                (let-when [#_"Object" op (first form)] (not (Compiler'isSpecial op)) => form
                    (let-when [#_"Var" v (Compiler'maybeMacro op, scope)] (some? v) => form
                        (apply v form @(get scope :'local-env) (next form))
                    )
                )
            )
        )
    )

    (defn #_"edn" Compiler'macroexpand [#_"edn" form, #_"map" scope]
        (let-when [#_"edn" f (Compiler'macroexpand1 form, scope)] (identical? f form) => (recur f, scope)
            form
        )
    )

    (defn #_"void" Compiler'closeOver [#_"LocalBinding" lb, #_"FnMethod" fm]
        (when (and (some? lb) (some? fm) (not (contains? @(:'locals fm) (:uid lb))))
            (swap! (:'closes (:fun fm)) assoc (:uid lb) lb)
            (Compiler'closeOver lb, (:parent fm))
        )
        nil
    )

    (defn #_"Expr" Compiler'analyzeSymbol [#_"Symbol" sym, #_"map" scope]
        (or
            (when (nil? (:ns sym))
                (when-some [#_"LocalBinding" lb (get @(get scope :'local-env) sym)]
                    (Compiler'closeOver lb, (get scope :fm))
                    (LocalBindingExpr'new lb)
                )
            )
            (let [#_"Object" o (Compiler'resolveIn *ns*, sym)]
                (cond
                    (var? o)
                        (when (nil? (Compiler'maybeMacro o, scope)) => (throw! (str "can't take value of a macro: " o))
                            (VarExpr'new o)
                        )
                    (symbol? o)
                        (UnresolvedVarExpr'new o)
                    :else
                        (throw! (str "unable to resolve symbol: " sym " in this context"))
                )
            )
        )
    )

    (defn #_"Expr" Compiler'analyzeSeq [#_"seq" form, #_"Context" context, #_"map" scope]
        (let-when [#_"Object" me (Compiler'macroexpand1 form, scope)] (= me form) => (Compiler'analyze me, context, scope)
            (when-some [#_"Object" op (first form)] => (throw! (str "can't call nil, form: " form))
                (let [#_"fn" f'parse (or (get Compiler'specials op) InvokeExpr'parse)]
                    (f'parse form, context, scope)
                )
            )
        )
    )

    (defn #_"Expr" Compiler'analyze
        ([#_"edn" form, #_"map" scope] (Compiler'analyze form, :Context'EXPRESSION, scope))
        ([#_"edn" form, #_"Context" context, #_"map" scope]
            (let [form
                    (when (satisfies? LazySeq form) => form
                        (with-meta (or (seq form) (list)) (meta form))
                    )]
                (case! form
                    nil                                  LiteralExpr'NIL
                    true                                 LiteralExpr'TRUE
                    false                                LiteralExpr'FALSE
                    (cond
                        (symbol? form)                   (Compiler'analyzeSymbol form, scope)
                        (string? form)                   (LiteralExpr'new (String''intern form))
                        (and (coll? form) (empty? form)) (LiteralExpr'new form)
                        (seq? form)                      (Compiler'analyzeSeq form, context, scope)
                        (vector? form)                   (VectorExpr'parse form, scope)
                        (map? form)                      (MapExpr'parse form, scope)
                        (set? form)                      (SetExpr'parse form, scope)
                        :else                            (LiteralExpr'new form)
                    )
                )
            )
        )
    )

    (defn #_"edn" Compiler'eval
        ([#_"edn" form] (Compiler'eval form, nil))
        ([#_"edn" form, #_"map" scope]
            (let [form (Compiler'macroexpand form, scope)]
                (-> (list (symbol! 'fn*) [] form)
                    (Compiler'analyze scope)
                    (Closure'new nil)
                    (IFn'''invoke)
                )
            )
        )
    )
)
)

(about #_"beagle.LispReader"

(about #_"LispReader"
    (defn #_"Symbol" LispReader'registerGensym [#_"map" scope, #_"Symbol" sym]
        (when (contains? scope :'gensym-env) => (throw! "gensym literal not in syntax-quote")
            (or (get @(get scope :'gensym-env) sym)
                (let [#_"Symbol" gsym (symbol (str (:name sym) "__" (next-id!) "__auto__"))]
                    (swap! (get scope :'gensym-env) assoc sym gsym)
                    gsym
                )
            )
        )
    )

    (declare LispReader'macros)

    (defn #_"boolean" LispReader'isMacro [#_"char" ch]
        (contains? LispReader'macros ch)
    )

    (defn #_"boolean" LispReader'isTerminatingMacro [#_"char" ch]
        (and (LispReader'isMacro ch) (not (any = ch \# \' \%)))
    )

    (defn #_"boolean" LispReader'isDigit [#_"char" ch, #_"int" base]
        (not= (Character'digit ch, base) -1)
    )

    (defn #_"boolean" LispReader'isWhitespace [#_"char" ch]
        (or (Character'isWhitespace ch) (= ch \,))
    )

    (defn #_"Character" LispReader'read1 [#_"Reader" r]
        (let [#_"int" c (Reader''read r)]
            (when-not (= c -1)
                (char c)
            )
        )
    )

    (defn #_"void" LispReader'unread [#_"PushbackReader" r, #_"Character" ch]
        (when (some? ch)
            (PushbackReader''unread r, (int ch))
        )
        nil
    )

    (defn #_"void" LispReader'consumeWhitespaces [#_"PushbackReader" r]
        (loop-when-recur [#_"char" ch (LispReader'read1 r)] (and (some? ch) (LispReader'isWhitespace ch)) [(LispReader'read1 r)] => (LispReader'unread r, ch))
        nil
    )

    (def #_"Pattern" LispReader'rxInteger #"[-+]?(?:0|[1-9][0-9]*)")

    (defn #_"Object" LispReader'matchNumber [#_"String" s]
        (let-when [#_"Matcher" m (Pattern''matcher LispReader'rxInteger, s)] (Matcher''matches m)
            (Integer'parseInt s)
        )
    )

    (defn #_"Object" LispReader'readNumber [#_"PushbackReader" r, #_"char" ch]
        (let [#_"String" s
                (let [#_"StringBuilder" sb (StringBuilder'new) _ (StringBuilder''append sb, ch)]
                    (loop []
                        (let [ch (LispReader'read1 r)]
                            (if (or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isMacro ch))
                                (do
                                    (LispReader'unread r, ch)
                                    (StringBuilder''toString sb)
                                )
                                (do
                                    (StringBuilder''append sb, ch)
                                    (recur)
                                )
                            )
                        )
                    )
                )]
            (or (LispReader'matchNumber s) (throw! (str "invalid number: " s)))
        )
    )

    (defn #_"String" LispReader'readToken [#_"PushbackReader" r, #_"char" ch]
        (let [#_"StringBuilder" sb (StringBuilder'new) _ (StringBuilder''append sb, ch)]
            (loop []
                (let [ch (LispReader'read1 r)]
                    (if (or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isTerminatingMacro ch))
                        (do
                            (LispReader'unread r, ch)
                            (StringBuilder''toString sb)
                        )
                        (do
                            (StringBuilder''append sb, ch)
                            (recur)
                        )
                    )
                )
            )
        )
    )

    (def #_"Pattern" LispReader'rxSymbol #"[:]?([\D&&[^/]].*/)?(/|[\D&&[^/]][^/]*)")

    (defn #_"Object" LispReader'matchSymbol [#_"String" s]
        (let-when [#_"Matcher" m (Pattern''matcher LispReader'rxSymbol, s)] (Matcher''matches m)
            (let [#_"String" ns (Matcher''group m, 1) #_"String" n (Matcher''group m, 2)]
                (cond
                    (or (and (some? ns) (String''endsWith ns, ":/")) (String''endsWith n, ":") (not= (String''indexOf s, "::", 1) -1))
                        nil
                    (String''startsWith s, "::")
                        (let [#_"Symbol" ks (symbol (String''substring s, 2))
                              #_"Namespace" kns (if (some? (:ns ks)) (Namespace''getAlias *ns*, (symbol (:ns ks))) *ns*)]
                            (when (some? kns)
                                (keyword (:name (:name kns)) (:name ks))
                            )
                        )
                    :else
                        (let [#_"boolean" kw? (= (String''charAt s, 0) \:) #_"Symbol" sym (symbol (String''substring s, (if kw? 1 0)))]
                            (if kw? (keyword sym) sym)
                        )
                )
            )
        )
    )

    (defn #_"Object" LispReader'interpretToken [#_"String" s]
        (case! s "nil" nil "true" true "false" false
            (or (LispReader'matchSymbol s) (throw! (str "invalid token: " s)))
        )
    )

    (defn #_"Object" LispReader'read
        ([#_"PushbackReader" r, #_"map" scope] (LispReader'read r, scope, true, nil))
        ([#_"PushbackReader" r, #_"map" scope, #_"boolean" eofIsError, #_"Object" eofValue] (LispReader'read r, scope, eofIsError, eofValue, nil, nil))
        ([#_"PushbackReader" r, #_"map" scope, #_"boolean" eofIsError, #_"Object" eofValue, #_"Character" returnOn, #_"Object" returnOnValue]
            (loop []
                (let [#_"char" ch (loop-when-recur [ch (LispReader'read1 r)] (and (some? ch) (LispReader'isWhitespace ch)) [(LispReader'read1 r)] => ch)]
                    (cond
                        (nil? ch)
                            (if eofIsError (throw! "EOF while reading") eofValue)
                        (and (some? returnOn) (= returnOn ch))
                            returnOnValue
                        (LispReader'isDigit ch, 10)
                            (LispReader'readNumber r, ch)
                        :else
                            (let [#_"fn" f'macro (get LispReader'macros ch)]
                                (if (some? f'macro)
                                    (let [#_"Object" o (f'macro r scope ch)]
                                        (recur-when (identical? o r) [] => o)
                                    )
                                    (or
                                        (when (any = ch \+ \-)
                                            (let [#_"char" ch' (LispReader'read1 r) _ (LispReader'unread r, ch')]
                                                (when (and (some? ch') (LispReader'isDigit ch', 10))
                                                    (LispReader'readNumber r, ch)
                                                )
                                            )
                                        )
                                        (LispReader'interpretToken (LispReader'readToken r, ch))
                                    )
                                )
                            )
                    )
                )
            )
        )
    )

    (def #_"any" LispReader'READ_EOF (anew 0))
    (def #_"any" LispReader'READ_FINISHED (anew 0))

    (defn #_"vector" LispReader'readDelimitedForms [#_"PushbackReader" r, #_"map" scope, #_"char" delim]
        (loop [#_"vector" v (vector)]
            (let [#_"Object" form (LispReader'read r, scope, false, LispReader'READ_EOF, delim, LispReader'READ_FINISHED)]
                (condp identical? form
                    LispReader'READ_EOF
                        (throw! "EOF while reading")
                    LispReader'READ_FINISHED
                        v
                    (recur (conj v form))
                )
            )
        )
    )
)

(about #_"RegexReader"
    (defn #_"Pattern" regex-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (let [#_"StringBuilder" sb (StringBuilder'new)]
            (loop []
                (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading regex")
                    (when-not (= ch \") ;; oops! "
                        (StringBuilder''append sb, ch)
                        (when (= ch \\)
                            (when-some [ch (LispReader'read1 r)] => (throw! "EOF while reading regex")
                                (StringBuilder''append sb, ch)
                            )
                        )
                        (recur)
                    )
                )
            )
            (Pattern'compile (StringBuilder''toString sb))
        )
    )
)

(about #_"StringReader"
    (defn #_"char" StringReader'escape [#_"PushbackReader" r]
        (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading string")
            (case! ch
                \t  \tab
                \r  \return
                \n  \newline
                \\  ch
                \"  ch ;; oops! "
                \b  \backspace
                \f  \formfeed
                (throw! (str "unsupported escape character: \\" ch))
            )
        )
    )

    (defn #_"Object" string-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (let [#_"StringBuilder" sb (StringBuilder'new)]
            (loop []
                (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading string")
                    (when-not (= ch \") ;; oops! "
                        (StringBuilder''append sb, (if (= ch \\) (StringReader'escape r) ch))
                        (recur)
                    )
                )
            )
            (StringBuilder''toString sb)
        )
    )
)

(about #_"DiscardReader"
    (defn #_"Object" discard-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (LispReader'read r, scope)
        r
    )
)

(about #_"QuoteReader"
    (defn #_"Object" quote-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (list (symbol! 'quote) (LispReader'read r, scope))
    )
)

(about #_"DerefReader"
    (defn #_"Object" deref-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (list (symbol! `deref) (LispReader'read r, scope))
    )
)

(about #_"VarReader"
    (defn #_"Object" var-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (list (symbol! 'var) (LispReader'read r, scope))
    )
)

(about #_"DispatchReader"
    (declare LispReader'dispatchMacros)

    (defn #_"Object" dispatch-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading character")
            (let-when [#_"fn" f'macro (get LispReader'dispatchMacros ch)] (nil? f'macro) => (f'macro r scope ch)
                (LispReader'unread r, ch)
                (throw! (str "no dispatch macro for: " ch))
            )
        )
    )
)

(about #_"MetaReader"
    (defn #_"Object" meta-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (let [#_"Object" _meta (LispReader'read r, scope)
              _meta
                (cond
                    (keyword? _meta) {_meta true}
                    (map? _meta)      _meta
                    :else (throw! "metadata must be Keyword or Map")
                )
              #_"Object" o (LispReader'read r, scope)]
            (when (satisfies? IMeta o) => (throw! "metadata can only be applied to IMetas")
                (if (satisfies? IReference o)
                    (do
                        (reset-meta! o _meta)
                        o
                    )
                    (let [#_"meta" m
                            (loop-when [m (meta o) #_"seq" s (seq _meta)] (some? s) => m
                                (let [#_"pair" e (first s)]
                                    (recur (assoc m (key e) (val e)) (next s))
                                )
                            )]
                        (with-meta o m)
                    )
                )
            )
        )
    )
)

(about #_"SyntaxQuoteReader"
(def unquote)

    (defn #_"boolean" SyntaxQuoteReader'isUnquote [#_"Object" form]
        (and (seq? form) (= (first form) `unquote))
    )

(def unquote-splicing)

    (defn #_"boolean" SyntaxQuoteReader'isUnquoteSplicing [#_"Object" form]
        (and (seq? form) (= (first form) `unquote-splicing))
    )

    (declare SyntaxQuoteReader'syntaxQuote)

    (defn #_"seq" SyntaxQuoteReader'sqExpandList [#_"map" scope, #_"seq" s]
        (loop-when [#_"vector" v (vector) s s] (some? s) => (seq v)
            (let [#_"Object" item (first s)
                  v (cond
                        (SyntaxQuoteReader'isUnquote item)         (conj v (list (symbol! `list) (second item)))
                        (SyntaxQuoteReader'isUnquoteSplicing item) (conj v (second item))
                        :else                                      (conj v (list (symbol! `list) (SyntaxQuoteReader'syntaxQuote scope, item)))
                    )]
                (recur v (next s))
            )
        )
    )

    (defn #_"Object" SyntaxQuoteReader'syntaxQuote [#_"map" scope, #_"Object" form]
        (let [#_"Object" q
                (cond
                    (Compiler'isSpecial form)
                        (list (symbol! 'quote) form)
                    (symbol? form)
                        (let [#_"String" ns (:ns form) #_"String" n (:name form)
                              form
                                (cond
                                    (and (nil? ns) (String''endsWith n, "#"))
                                        (LispReader'registerGensym scope, (symbol (String''substring n, 0, (dec (String''length n)))))
                                    (and (nil? ns) (String''endsWith n, "."))
                                        (symbol (str (:name (Compiler'resolveSymbol (symbol (String''substring n, 0, (dec (String''length n)))))) "."))
                                    (and (nil? ns) (String''startsWith n, "."))
                                        form
                                    :else
                                        (Compiler'resolveSymbol form)
                                )]
                            (list (symbol! 'quote) form)
                        )
                    (SyntaxQuoteReader'isUnquote form)
                        (second form)
                    (SyntaxQuoteReader'isUnquoteSplicing form)
                        (throw! "splice not in list")
                    (coll? form)
                        (cond
                            (map? form)
                                (list (symbol! `apply) (symbol! `array-map) (list (symbol! `seq) (cons (symbol! `concat) (SyntaxQuoteReader'sqExpandList scope, (seq (mapcat identity form))))))
                            (vector? form)
                                (list (symbol! `apply) (symbol! `vector) (list (symbol! `seq) (cons (symbol! `concat) (SyntaxQuoteReader'sqExpandList scope, (seq form)))))
                            (set? form)
                                (list (symbol! `apply) (symbol! `array-set) (list (symbol! `seq) (cons (symbol! `concat) (SyntaxQuoteReader'sqExpandList scope, (seq form)))))
                            (or (seq? form) (list? form))
                                (when-some [#_"seq" s (seq form)] => (cons (symbol! `list) nil)
                                    (list (symbol! `seq) (cons (symbol! `concat) (SyntaxQuoteReader'sqExpandList scope, s)))
                                )
                            :else
                                (throw! "unknown collection type")
                        )
                    (or (keyword? form) (number? form) (char? form) (string? form))
                        form
                    :else
                        (list (symbol! 'quote) form)
                )]
            (when (and (satisfies? IObj form) (seq (meta form)) (not (SyntaxQuoteReader'isUnquote form))) => q
                (list (symbol! `with-meta) q (SyntaxQuoteReader'syntaxQuote scope, (meta form)))
            )
        )
    )

    (defn #_"Object" syntax-quote-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (let [scope (assoc scope :'gensym-env (atom (array-map)))]
            (SyntaxQuoteReader'syntaxQuote scope, (LispReader'read r, scope))
        )
    )
)

(about #_"UnquoteReader"
    (defn #_"Object" unquote-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading character")
            (if (= ch \@)
                (list (symbol! `unquote-splicing) (LispReader'read r, scope))
                (do
                    (LispReader'unread r, ch)
                    (list (symbol! `unquote) (LispReader'read r, scope))
                )
            )
        )
    )
)

(about #_"CharacterReader"
    (defn #_"Object" character-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (when-some [#_"char" ch (LispReader'read1 r)] => (throw! "EOF while reading character")
            (let [#_"String" token (LispReader'readToken r, ch)]
                (when-not (= (String''length token) 1) => (Character'valueOf (String''charAt token, 0))
                    (case! token
                        "newline"   \newline
                        "space"     \space
                        "tab"       \tab
                        "backspace" \backspace
                        "formfeed"  \formfeed
                        "return"    \return
                        (throw! (str "unsupported character: \\" token))
                    )
                )
            )
        )
    )
)

(about #_"ListReader"
    (defn #_"Object" list-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (apply list (LispReader'readDelimitedForms r, scope, \)))
    )
)

(about #_"VectorReader"
    (defn #_"Object" vector-reader [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (vec (LispReader'readDelimitedForms r, scope, \]))
    )
)

(about #_"UnmatchedDelimiterReader"
    (defn #_"Object" unmatched-delimiter-reader [#_"PushbackReader" _r, #_"map" scope, #_"char" delim]
        (throw! (str "unmatched delimiter: " delim))
    )
)

(about #_"LispReader"
    (def #_"{char fn}" LispReader'macros
        (array-map
            \"  string-reader ;; oops! "
            \'  quote-reader
            \@  deref-reader
            \^  meta-reader
            \`  syntax-quote-reader
            \~  unquote-reader
            \(  list-reader,    \)  unmatched-delimiter-reader
            \[  vector-reader,  \]  unmatched-delimiter-reader
            \\  character-reader
            \#  dispatch-reader
        )
    )

    (def #_"{char fn}" LispReader'dispatchMacros
        (array-map
            \^  meta-reader
            \'  var-reader
            \"  regex-reader ;; oops! "
            \_  discard-reader
        )
    )
)
)

(defn read
    ([] (read -/*in*))
    ([s] (read s true nil))
    ([s eof-error? eof-value] (LispReader'read s, nil, (boolean eof-error?), eof-value))
)

(about #_"Beagle"

(about #_"*ns*"
    (swap! Namespace'namespaces assoc 'clojure.core (-/the-ns 'clojure.core), 'beagle.bore (-/the-ns 'beagle.bore))

    (def #_"Var" ^:dynamic *ns* (create-ns (symbol "beagle.core")))

    (defn refer* [& s*]
        (doseq [#_"symbol" s s*]
            (let [#_"class|var" v (-/ns-resolve -/*ns* (-/symbol (str s)))]
                (intern *ns*, (with-meta (symbol! s) (when (var? v) (-/select-keys (meta v) [:dynamic :macro]))), (if (var? v) @v v))
            )
        )
    )

    (apply refer* '[& + - < << <= = > >> >= A'clone A'get A'length alter-var-root A'new Appendable''append apply array? Array'get Array'getLength array-map A'set AtomicReference''compareAndSet AtomicReference''get AtomicReference'new AtomicReference''set boolean char char? Character'digit Character'isWhitespace Character'valueOf clojure-ilookup? clojure-keyword? clojure-namespace? clojure-symbol? clojure-var? concat cons count dec defmacro defn deref even? first Flushable''flush fn identical? ILookup''valAt inc int int! int? Integer'parseInt Integer'valueOf interleave keyword? Keyword''sym let list list* loop map mapcat matcher? Matcher''group Matcher''groupCount Matcher''matches meta M'get Mutable''mutate! Namespace''-findInternedVar Namespace''-getMapping Namespace''-getMappings Namespace''-intern neg? new* next not= nth number? Number''toString Object''toString odd? partial partition pattern? Pattern'compile Pattern''matcher Pattern''pattern pos? PrintWriter''println PushbackReader''unread Reader''read refer* satisfies? second seq seq? split-at str string? String''charAt String''endsWith String''indexOf String''intern String''length String''startsWith String''substring StringBuilder''append StringBuilder'new StringBuilder''toString symbol? System'arraycopy throw! Var''-alterRoot Var''-get Var''-hasRoot Var''-isBound Var''setMacro vary-meta vec vector vector? with-meta zero?])

    (alias (symbol "-"), (the-ns 'clojure.core))
)

(defn repl []
    (let [#_"map" scope (array-map :'local-env (atom (array-map)))]
        (loop []
            (print "\033[31mBeagle \033[32m=> \033[0m")
            (flush)
            (-> (read) (Compiler'eval scope) (prn))
            (recur)
        )
    )
)
)

(defn -main [& args])
