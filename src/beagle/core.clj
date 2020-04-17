(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* = aclone aget alength alter-var-root apply aset assoc case class class? complement concat conj defn defn- defonce deref disj doseq drop drop-while eval every? find-protocol-method first fn gensym import interleave keys keyword let list list* loop mapcat merge meta munge namespace-munge next ns-imports ns-name ns-resolve ns-unmap object-array range read-string resolve second select-keys seq seq? set some some? take-nth take-while var-get vary-meta vector with-meta])
    (:require [clojure.core :as -])
)

(-/defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (ns-imports *ns*))] (ns-unmap *ns* n#)) (import ~@syms-or-seqs)))

(import!
    [java.lang Appendable Character Class Error Integer Long Number Object String StringBuilder System]
    [java.lang.reflect Array Constructor]
    [java.io Flushable PrintWriter PushbackReader Reader]
    [java.util.regex Matcher Pattern]
    [clojure.lang Associative Counted DynamicClassLoader IAtom IFn ILookup IPersistentMap ISeq Namespace Seqable Var]
    [beagle.util.concurrent.atomic AtomicReference]
)

(-/defmacro refer! [ns s]
    (-/let [f (fn [%] (-/let [v (ns-resolve (-/the-ns ns) %) n (vary-meta % merge (select-keys (meta v) [:macro]))] `(def ~n ~(var-get v))))]
        (if (-/symbol? s) (f s) (-/cons 'do (-/map f s)))
    )
)

(refer! clojure.core [< <= == array-map bit-and bit-shift-left bit-shift-right char cons defmacro doall get identical? instance? int keyword? map name namespace nth satisfies? str symbol symbol? the-ns unchecked-add-int unchecked-dec-int unchecked-inc-int unchecked-subtract-int vals vec vector?])

(defmacro about [& s] (cons 'do s))

(defn throw! [#_"String" s] (throw (Error. s)))

(defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))

(defn char? [x] (instance? Character x))

(defn #_"int"       Character'digit        [#_"char" ch, #_"int" radix] (Character/digit ch, radix))
(defn #_"boolean"   Character'isWhitespace [#_"char" ch]                (Character/isWhitespace ch))
(defn #_"Character" Character'valueOf      [#_"char" ch]                (Character/valueOf ch))

(defn int? [x] (-/or (instance? Integer x) (instance? Long x)))

(defn #_"int" Integer'parseInt [#_"String" s] (Integer/parseInt s))

(defn number? [x] (instance? Number x))

(defn int! [^Number n] (.intValue n))

(defn #_"String" Number''toString [^Number this] (.toString this))

(defn #_"boolean" Object''equals   [^Object this, #_"Object" that] (.equals this, that))
(defn #_"String"  Object''toString [^Object this]                  (.toString this))

(defn string? [x] (instance? String x))

(defn #_"char"    String''charAt     [^String this, #_"int" i]    (.charAt this, i))
(defn #_"int"     String''indexOf   ([^String this, #_"int" ch]   (.indexOf this, ch))     ([^String this, #_"String" s, #_"int" from] (.indexOf this, s, from)))
(defn #_"int"     String''length     [^String this]               (.length this))
(defn #_"String"  String''substring ([^String this, #_"int" from] (.substring this, from)) ([^String this, #_"int" from, #_"int" over] (.substring this, from, over)))

(defn #_"StringBuilder" StringBuilder'new [] (StringBuilder.))

(defn #_"StringBuilder" StringBuilder''append   [^StringBuilder this, #_"char" ch] (.append this, ch))
(defn #_"String"        StringBuilder''toString [^StringBuilder this]              (.toString this))

(defn #_"void" System'arraycopy [#_"array" a, #_"int" i, #_"array" b, #_"int" j, #_"int" n] (System/arraycopy a, i, b, j, n))

(def System'in  *in*)
(def System'out *out*)

(defn array? [x] (.isArray (class x)))

(defn #_"int" Array'getLength [#_"array" a] (Array/getLength a))

(defn clojure-counted? [x] (instance? clojure.lang.Counted x))

(defn #_"int" Counted''count [^Counted this] (.count this))

(defn #_"void" Flushable''flush [^Flushable this] (.flush this))

(defn #_"void" PushbackReader''unread [^PushbackReader this, #_"int" x] (.unread this, x))

(defn #_"int" Reader''read [^Reader this] (.read this))

(defn #_"Pattern" Pattern'compile  [#_"String" s]                (Pattern/compile s))
(defn #_"Matcher" Pattern''matcher [^Pattern this, #_"String" s] (.matcher this, s))

(defn #_"boolean" Matcher''matches [^Matcher this] (.matches this))

(defn clojure-deref? [x] (instance? clojure.lang.IDeref x))

(defn #_"Object" IDeref''deref [#_"IDeref" this] (.deref this))

(defn clojure-atom? [x] (instance? clojure.lang.IAtom))

(defn #_"Object" IAtom''swap  [^IAtom this, #_"fn" f, #_"seq" s] (.swap  this, f, s))
(defn #_"Object" IAtom''reset [^IAtom this, #_"Object" x]        (.reset this, x))

(def #_"var" Compiler'LOADER clojure.lang.Compiler/LOADER)

(defn #_"Class" DynamicClassLoader''defineClass [^DynamicClassLoader this, #_"String" name, #_"byte[]" bytes, #_"form" _] (.defineClass this, name, bytes, _))

(defn clojure-fn? [x] (instance? clojure.lang.IFn x))

(defn #_"Object" IFn''applyTo [^IFn this, #_"seq" args] (.applyTo this, args))

(defn clojure-seqable? [x] (instance? clojure.lang.Seqable x))

(defn #_"seq" Seqable''seq [^Seqable this] (.seq this))

(defn clojure-seq? [x] (instance? clojure.lang.ISeq x))

(defn #_"Object" ISeq''first [^ISeq this] (.first this))
(defn #_"seq" ISeq''next [^ISeq this] (.next this))

(defn clojure-associative? [x] (instance? clojure.lang.Associative x))

(defn #_"Associative" Associative''assoc [^Associative this, #_"key" key, #_"value" val] (.assoc this, key, val))
(defn #_"boolean" Associative''containsKey [^Associative this, #_"key" key] (.containsKey this, key))

(defn clojure-ilookup? [x] (instance? clojure.lang.ILookup x))

(defn #_"value" ILookup''valAt [^ILookup this, #_"key" key] (.valAt this, key))

(defn clojure-map? [x] (instance? clojure.lang.IPersistentMap x))

(defn #_"IPersistentMap" IPersistentMap''dissoc [^IPersistentMap this, #_"key" key] (.without this, key))

(defn #_"var" Namespace''findInternedVar [^Namespace this, #_"Symbol" name] (.findInternedVar this, name))

(defn clojure-symbol? [x] (instance? clojure.lang.Symbol x))

(defn clojure-var? [x] (instance? clojure.lang.Var x))

(defn #_"Object" Var''-get [^Var this] (.get this))

(defn #_"AtomicReference" AtomicReference'new [#_"any" init] (AtomicReference. init))

(defn #_"boolean" AtomicReference''compareAndSet [^AtomicReference this, #_"any" x, #_"any" y] (.compareAndSet this, x, y))
(defn #_"any"     AtomicReference''get           [^AtomicReference this]                       (.get this))
(defn #_"void"    AtomicReference''set           [^AtomicReference this, #_"any" x]            (.set this, x))

(defn A'new [n] (object-array n))

(defn A'clone  [^"[Ljava.lang.Object;" a]     (aclone a))
(defn A'get    [^"[Ljava.lang.Object;" a i]   (aget a i))
(defn A'length [^"[Ljava.lang.Object;" a]     (alength a))
(defn A'set    [^"[Ljava.lang.Object;" a i x] (aset a i x))

(defn new* [^Class c & s] (.newInstance ^Constructor (first (.getConstructors c)), (A'new s)))

(defn- gen-interface* [sym]
    (DynamicClassLoader''defineClass (var-get Compiler'LOADER), (str sym), (second (#'-/generate-interface (array-map (keyword (name :name)) sym))), nil)
)

(defn- emit-defproto* [name sigs]
    (let [
        iname (symbol (str (munge (namespace-munge *ns*)) "." (munge name)))
    ]
        `(do
            (defonce ~name (array-map))
            (#'gen-interface* '~iname)
            (alter-var-root (var ~name) merge
                ~(array-map :var (list 'var name), :on (list 'quote iname), :on-interface (list `resolve (list 'quote iname)))
            )
            ~@(map (fn [[f & _]] `(defmacro ~f [x# & s#] (list* (list find-protocol-method '~name ~(keyword (str f)) x#) x# s#))) sigs)
            '~name
        )
    )
)

(defmacro defproto [name & sigs]
    (emit-defproto* name sigs)
)

(defn- parse-opts [s]
    (loop [opts (array-map) [k v & rs :as s] s] (if (keyword? k) (recur (assoc opts k v) rs) [opts s]))
)

(defn- parse-impls [specs]
    (loop [impls (array-map) s specs] (if (seq s) (recur (assoc impls (first s) (take-while seq? (next s))) (drop-while seq? (next s))) impls))
)

(defn- parse-opts+specs [opts+specs]
    (let [
        [opts specs] (parse-opts opts+specs)
        impls        (parse-impls specs)
        interfaces   (-/-> (map (fn [%] (if ((complement class?) (resolve %)) (:on (deref (resolve %))) %)) (keys impls)) set (disj 'Object 'java.lang.Object) vec)
        methods      (map (fn [[name params & body]] (cons name (#'-/maybe-destructured params body))) (apply concat (vals impls)))
    ]
        [interfaces methods opts]
    )
)

(defn- emit-defarray* [tname cname fields interfaces methods opts]
    (let [
        classname  (with-meta (symbol (str (namespace-munge *ns*) "." cname)) (meta cname))
        interfaces (vec interfaces)
        fields     (map (fn [%] (with-meta % nil)) fields)
    ]
        (let [a '__array s (mapcat (fn [x y] [(name y) x]) (range) fields)]
            (let [ilookup
                    (fn [[i m]]
                        [
                            (conj i 'clojure.lang.ILookup)
                            (conj m
                                `(valAt [this# k#] (-/when-some [x# (case (name k#) ~@s nil)] (aget (. this# ~a) x#)))
                            )
                        ]
                    )]
                (let [[i m] (-/-> [interfaces methods] ilookup)]
                    `(eval '~(read-string (str (list* 'deftype* (symbol (name (ns-name *ns*)) (name tname)) classname (vector a) :implements (vec i) m))))
                )
            )
        )
    )
)

(defmacro defarray [name fields & opts+specs]
    (let [[interfaces methods opts] (parse-opts+specs opts+specs)]
        `(do
            ~(emit-defarray* name name (vec fields) (vec interfaces) methods opts)
            (eval '~(list (symbol "clojure.core/import*") (str (namespace-munge *ns*) "." name)))
        )
    )
)

(defmacro defp [p & s]                                      `(do (defproto ~p ~@s)             '~p))
(defmacro defq [r f & s] (let [c (symbol (str r "'class"))] `(do (defarray ~c ~(vec f) ~r ~@s) '~c)))

(defmacro declare [& names] `(do ~@(map (fn [%] (list 'def %)) names)))

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

(let [=> (fn [s] (if (= '=> (first s)) (next s) (cons nil s)))]
    (defmacro     when       [? & s] (let [[e & s] (=> s)]               `(if     ~? (do ~@s) ~e)))
    (defmacro     when-not   [? & s] (let [[e & s] (=> s)]               `(if-not ~? (do ~@s) ~e)))
    (defmacro let-when     [v ? & s] (let [[e & s] (=> s)] `(let ~(vec v) (if     ~? (do ~@s) ~e))))
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

(let [=> (fn [s] (if (= '=> (first s)) (next s) (cons nil s)))]
    (defmacro when-some [v & s] (let [[e & s] (=> s)] `(if-some ~(vec v) (do ~@s) ~e)))
)

(let [v' (fn [v] (cond (vector? v) v (symbol? v) [v v] :else [`_# v]))
      r' (fn [r] (cond (vector? r) `((recur ~@r)) (some? r) `((recur ~r))))
      => (fn [s] (if (= '=> (first s)) (next s) (cons nil s)))
      l' (fn [v ? r s] (let [r (r' r) [e & s] (=> s)] `(loop ~(v' v) (if ~? (do ~@s ~@r) ~e))))]
    (defmacro loop-when [v ? & s] (l' v ? nil s))
    (defmacro loop-when-recur [v ? r & s] (l' v ? r s))
)

(let [r' (fn [r] (cond (vector? r) `(recur ~@r) (some? r) `(recur ~r)))
      => (fn [s] (if (= '=> (first s)) (second s)))]
    (defmacro recur-when [? r & s] `(if ~? ~(r' r) ~(=> s)))
)

(defmacro -> [x & s]
    (when s => x
        (recur &form &env
            (let-when [f (first s)] (seq? f) => (list f x)
                `(~(first f) ~x ~@(next f))
            )
            (next s)
        )
    )
)

(ns beagle.core
    (:refer-clojure :only [])
    (:require [beagle.bore :as -])
)

(-/import!)

(-/defmacro λ    [& s] (-/cons 'fn* s))
(-/defmacro let  [& s] (-/cons 'let* s))
(-/defmacro loop [& s] (-/cons 'loop* s))

(def ? -/ILookup''valAt)

(def identical? -/identical?)

(def comp (λ [f g] (λ [x] (f (g x)))))

(def nil?  (λ [x] (identical? x nil)))
(def not   (λ [x] (if x false true)))
(def some? (λ [x] (not (nil? x))))

(-/about #_"beagle.Seqable"
    (-/declare Cons MSeq PersistentMap)

    (def seqable? (λ [x] (-/or (nil? x) (-/satisfies? Cons x) (-/satisfies? MSeq x) (-/satisfies? PersistentMap x) (-/clojure-seqable? x))))

    (-/declare Cons''seq MSeq''seq PersistentMap''seq str)

    (def seq (λ [x]
        (-/cond
            (nil? x)                       nil
            (-/satisfies? Cons x)          (Cons''seq x)
            (-/satisfies? MSeq x)          (MSeq''seq x)
            (-/satisfies? PersistentMap x) (PersistentMap''seq x)
            (-/clojure-seqable? x)         (-/Seqable''seq x)
            :else                          (-/throw! (str "seq not supported on " x))
        )
    ))
)

(-/about #_"beagle.ISeq"
    (def seq? (λ [x] (-/or (-/satisfies? Cons x) (-/satisfies? MSeq x) (-/clojure-seq? x))))

    (-/declare Cons''first MSeq''first)

    (def Seq''first (λ [s]
        (-/cond
            (-/satisfies? Cons s) (Cons''first s)
            (-/satisfies? MSeq s) (MSeq''first s)
            (-/clojure-seq? s)    (-/ISeq''first s)
            :else                 (-/throw! (str "first not supported on " s))
        )
    ))

    (-/declare Cons''next MSeq''next)

    (def Seq''next  (λ [s]
        (-/cond
            (-/satisfies? Cons s) (Cons''next s)
            (-/satisfies? MSeq s) (MSeq''next s)
            (-/clojure-seq? s)    (-/ISeq''next s)
            :else                 (-/throw! (str "next not supported on " s))
        )
    ))

    (def first (λ [s] (if (seq? s) (Seq''first s) (-/when-some [s (seq s)] (Seq''first s)))))
    (def next  (λ [s] (if (seq? s) (Seq''next s)  (-/when-some [s (seq s)] (Seq''next s)))))

    (def second (λ [s] (first (next s))))
    (def third  (λ [s] (first (next (next s)))))
    (def fourth (λ [s] (first (next (next (next s))))))

    (def reduce (λ [f r s] (-/if-some [s (seq s)] (recur f (f r (first s)) (next s)) r)))

    (def reduce-kv (λ [f r kvs] (-/if-some [kvs (seq kvs)] (recur f (f r (first kvs) (second kvs)) (next (next kvs))) r)))
)

(-/about #_"beagle.Counted"
    (-/declare Cons''count MSeq''count PersistentMap''count neg? < inc)

    (def count' (λ [x m]
        (-/cond
            (nil? x)                       0
            (-/array? x)                   (-/Array'getLength x)
            (-/string? x)                  (-/String''length x)
            (-/clojure-counted? x)         (-/Counted''count x)
            (-/satisfies? Cons x)          (Cons''count x)
            (-/satisfies? MSeq x)          (MSeq''count x)
            (-/satisfies? PersistentMap x) (PersistentMap''count x)
            (seqable? x)                   (-/loop-when-recur [n 0 s (seq x)] (-/and (some? s) (-/or (neg? m) (< n m))) [(inc n) (next s)] => n)
            :else                          (-/throw! (str "count not supported on " x))
        )
    ))

    (def count (λ [x] (count' x -1)))
)

(-/about #_"beagle.Atom"
    (-/defp Atom)
)

(-/about #_"beagle.Symbol"
    (-/defp Symbol)

    (def symbol? (λ [x] (-/or (-/satisfies? Symbol x) (-/clojure-symbol? x))))
)

(-/about #_"beagle.Cons"
    (-/defp Cons)
)

(-/about #_"beagle.PersistentMap"
    (-/defp MSeq)
    (-/defp PersistentMap)

    (def map? (λ [x] (-/or (-/satisfies? PersistentMap x) (-/clojure-map? x))))
)

(-/about #_"beagle.IDeref"
    (-/declare Atom''deref)

    (def derefable? (λ [x] (-/or (-/satisfies? Atom x) (-/clojure-deref? x))))

    (def deref (λ [x]
        (-/cond
            (-/satisfies? Atom x) (Atom''deref x)
            (-/clojure-deref? x)  (-/IDeref''deref x)
            :else                 (-/throw! (str "deref not supported on " x))
        )
    ))
)

(-/about #_"beagle.Closure"
    (-/defp Closure)

    (-/declare spread Closure''applyTo)

    (def apply (λ [f & s]
        (let [s (spread s)]
            (-/cond
                (-/satisfies? Closure f) (Closure''applyTo f, s)
                (derefable? f)           (apply (deref f) s)
                (-/clojure-fn? f)        (-/IFn''applyTo f, s)
                :else                    (-/throw! (str "apply not supported on " f))
            )
        )
    ))
)

(-/about #_"arrays"
    (def aget    (λ [a i] (-/A'get a i)))
    (def alength (λ [a]   (-/A'length a)))

    (def aclone (λ [a]         (-/when (some? a) (-/A'clone a))))
    (def acopy! (λ [a i b j n] (-/System'arraycopy b, j, a, i, n) a))
    (def aset!  (λ [a i x]     (-/A'set a i x) a))
    (def aswap! (λ [a i f & s] (aset! a i (apply f (aget a i) s))))

    (def anew (λ [size-or-seq]
        (if (-/number? size-or-seq)
            (-/A'new (-/int! size-or-seq))
            (let [#_"seq" s (seq size-or-seq) #_"int" n (count s)]
                (-/loop-when-recur [#_"array" a (-/A'new n) #_"int" i 0 s s] (-/and (< i n) (some? s)) [(aset! a i (first s)) (inc i) (next s)] => a)
            )
        )
    ))
)

(-/about #_"append, str, pr, prn"
    (def #_"{char String}" char-name-string
        (-/array-map
            \newline "newline"
            \space   "space"
        )
    )

    (def #_"Appendable" append-chr (λ [#_"Appendable" a, #_"char" x]
        (-/-> a (-/Appendable''append "\\") (-/Appendable''append (-/get char-name-string x x)))
    ))

    (def #_"{char String}" char-escape-string
        (-/array-map
            \newline "\\n"
            \"       "\\\""
            \\       "\\\\"
        )
    )

    (def #_"Appendable" append-str (λ [#_"Appendable" a, #_"String" x]
        (let [
            a (-/Appendable''append a, "\"")
            a (reduce (λ [%1 %2] (-/Appendable''append %1, (-/get char-escape-string %2 %2))) a x)
            a (-/Appendable''append a, "\"")
        ]
            a
        )
    ))

    (def #_"Appendable" append-sym (λ [#_"Appendable" a, #_"Symbol" x]
        (if (some? (? x :ns))
            (let [
                a (-/Appendable''append a, (? x :ns))
                a (-/Appendable''append a, "/")
                a (-/Appendable''append a, (? x :name))
            ]
                a
            )
            (-/Appendable''append a, (? x :name))
        )
    ))

    (def #_"Appendable" append* (λ [#_"Appendable" a, #_"String" b, #_"fn" f'append, #_"String" c, #_"String" d, #_"Seqable" q]
        (let [a (-/let-when [a (-/Appendable''append a, b) #_"seq" s (seq q)] (some? s) => a
                    (loop [a a s s]
                        (-/let-when [a (f'append a (first s)) s (next s)] (some? s) => a
                            (recur (-/Appendable''append a, c) s)
                        )
                    )
                )]
            (-/Appendable''append a, d)
        )
    ))

    (-/declare append)

    (def #_"Appendable" append-seq (λ [#_"Appendable" a, #_"seq" x] (append* a "(" append " " ")" x)))
    (def #_"Appendable" append-vec (λ [#_"Appendable" a, #_"vec" x] (append* a "[" append " " "]" x)))
    (def #_"Appendable" append-map (λ [#_"Appendable" a, #_"map" x] (append* a "{" (λ [a e] (-/-> a (append (first e)) (-/Appendable''append " ") (append (second e)))) ", " "}" x)))

    (-/declare =)

    (def #_"Appendable" append (λ [#_"Appendable" a, #_"any" x]
        (-/cond
            (= x nil)     (-/Appendable''append a, "nil")
            (= x false)   (-/Appendable''append a, "false")
            (= x true)    (-/Appendable''append a, "true")
            (-/number? x) (-/Appendable''append a, (-/Number''toString x))
            (-/string? x) (append-str a x)
            (symbol? x)   (append-sym a x)
            (seq? x)      (append-seq a x)
            (-/vector? x) (append-vec a x)
            (map? x)      (append-map a x)
            (-/char? x)   (append-chr a x)
            :else         (-/Appendable''append a, (-/Object''toString x))
        )
    ))

    (def #_"Appendable" append! (λ [#_"Appendable" a, #_"any" x]
        (if (-/or (-/symbol? x) (-/string? x) (-/char? x)) (-/Appendable''append a, x) (append a x))
    ))

    (def #_"String" str (λ
        ([] "")
        ([x] (if (some? x) (-/-> (-/StringBuilder'new) (append! x) (-/StringBuilder''toString)) ""))
        ([x & s]
            ((λ [#_"StringBuilder" sb s] (-/recur-when s [(append! sb (first s)) (next s)] => (-/StringBuilder''toString sb)))
                (-/-> (-/StringBuilder'new) (append! x)) s
            )
        )
    ))

    (def space   (λ [] (-/Appendable''append -/System'out \space)   nil))
    (def newline (λ [] (-/Appendable''append -/System'out \newline) nil))
    (def flush   (λ [] (-/Flushable''flush   -/System'out)          nil))

    (def pr (λ
        ([] nil)
        ([x] (append -/System'out x) nil)
        ([x & s]
            (pr x) (space)
            (-/let-when [x (first s) s (next s)] (some? s) => (pr x)
                (recur x s)
            )
        )
    ))

    (def print (λ
        ([] nil)
        ([x] (append! -/System'out x) nil)
        ([x & s]
            (print x) (space)
            (-/let-when [x (first s) s (next s)] (some? s) => (print x)
                (recur x s)
            )
        )
    ))

    (def prn     (λ [& s] (apply pr    s) (newline) (flush) nil))
    (def println (λ [& s] (apply print s) (newline) (flush) nil))
)

(-/about #_"beagle.Atom"

(-/about #_"Atom"
    (-/declare Atom''deref)

    (-/defq Atom [#_"AtomicReference" data]
        java.util.concurrent.Future (get [_] (Atom''deref _))
    )

    (def #_"Atom" Atom'new (λ [#_"Object" data]
        (-/new* Atom'class (anew [(-/AtomicReference'new data)]))
    ))

    (def #_"Object" Atom''deref (λ [#_"Atom" this]
        (-/AtomicReference''get (? this :data))
    ))

    (def #_"Object" Atom''swap (λ [#_"Atom" this, #_"fn" f, #_"seq" args]
        (loop []
            (let [#_"Object" o (-/AtomicReference''get (? this :data)) #_"Object" o' (apply f o args)]
                (-/when (-/AtomicReference''compareAndSet (? this :data), o, o') => (recur)
                    o'
                )
            )
        )
    ))

    (def #_"Object" Atom''reset (λ [#_"Atom" this, #_"Object" o']
        (-/AtomicReference''set (? this :data), o')
        o'
    ))
)

(def atom (λ [x] (Atom'new x)))

(def swap! (λ [a f & s]
    (-/cond
        (-/satisfies? Atom a) (Atom''swap a, f, s)
        (-/clojure-atom? a)   (-/IAtom''swap a, f, s)
        :else                 (-/throw! (str "swap! not supported on " a))
    )
))

(def reset! (λ [a x]
    (-/cond
        (-/satisfies? Atom a) (Atom''reset a, x)
        (-/clojure-atom? a)   (-/IAtom''reset a, x)
        :else                 (-/throw! (str "reset! not supported on " a))
    )
))
)

(-/about #_"beagle.IObject"

(-/about #_"IObject"
    (-/declare Symbol''equals Cons''equals MSeq''equals PersistentMap''equals)

    (def #_"boolean" IObject''equals (λ [#_"Object" a, #_"Object" b]
        (-/cond
            (-/satisfies? Symbol a)        (Symbol''equals a, b)
            (-/satisfies? Cons a)          (Cons''equals a, b)
            (-/satisfies? MSeq a)          (MSeq''equals a, b)
            (-/satisfies? PersistentMap a) (PersistentMap''equals a, b)
            (-/satisfies? Atom a)          (identical? a, b)
            :else                          (-/Object''equals a, b)
        )
    ))
)

(def = (λ [x y]
    (-/cond
        (identical? x y)              true
        (nil? x)                      false
        (-/and (-/number? x) (-/number? y)) (-/== x y)
        (-/or (seq? x) (map? x) (-/vector? x)) (IObject''equals x, y)
        (-/or (seq? y) (map? y) (-/vector? y)) (IObject''equals y, x)
        (-/instance? (-/get Symbol :on-interface) x) (Symbol''equals x, y)
        (-/instance? (-/get Symbol :on-interface) y) (Symbol''equals y, x)
        :else                         (IObject''equals x, y)
    )
))

(def not= (λ [x y] (not (= x y))))
)

(-/about #_"beagle.Numbers"

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
)

(-/about #_"beagle.Symbol"

(-/about #_"Symbol"
    (-/defq Symbol [#_"String" ns, #_"String" name]
        clojure.lang.Named (getNamespace [_] (? _ :ns)) (getName [_] (? _ :name))
        java.lang.Object (equals [_, o] (Symbol''equals _, o)) (toString [_] (str _))
    )

    (def #_"Symbol" Symbol'new (λ [#_"String" ns, #_"String" name]
        (-/new* Symbol'class (anew [ns, name]))
    ))

    (def #_"Symbol" Symbol'intern (λ [#_"String" nsname]
        (let [#_"int" i (-/String''indexOf nsname, (-/int \/))]
            (if (-/or (= i -1) (= nsname "/"))
                (Symbol'new nil, nsname)
                (Symbol'new (-/String''substring nsname, 0, i), (-/String''substring nsname, (inc i)))
            )
        )
    ))

    (def #_"boolean" Symbol''equals (λ [#_"Symbol" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (symbol? that)
                (= (? this :ns) (if (-/clojure-symbol? that) (-/namespace that) (? that :ns)))
                (= (? this :name) (if (-/clojure-symbol? that) (-/name that) (? that :name)))
            )
            (-/and (-/keyword? that)
                (= (? this :name) (-/str that))
            )
        )
    ))
)

(def symbol (λ [name] (if (symbol? name) name (Symbol'intern name))))

(def symbol! (λ [s] (symbol (if (-/clojure-symbol? s) (str s) s))))
)

(-/about #_"beagle.Closure"

(-/about #_"Closure"
    (-/declare Closure''applyTo)

    (-/defq Closure [#_"FnExpr" fun, #_"map'" _env]
        clojure.lang.IFn (applyTo [_, args] (Closure''applyTo _, args))
    )

    (def #_"Closure" Closure'new (λ [#_"FnExpr" fun, #_"map" env]
        (-/new* Closure'class (anew [fun, (atom env)]))
    ))

    (def #_"void" Closure'throwArity (λ [#_"fn" f, #_"int" n]
        (-/throw! (str "wrong number of args (" (if (neg? n) (str "more than " (dec (- 0 n))) n) ") passed to " f))
    ))

    (-/declare Compiler'MAX_POSITIONAL_ARITY Machine'compute FnMethod''compile)

    (-/declare get)

    (def #_"Object" Closure''applyTo (λ [#_"Closure" this, #_"seq" args]
        (let [
            #_"FnMethod" fm
                (let [#_"int" m (inc Compiler'MAX_POSITIONAL_ARITY) #_"int" n (min (count' args m) m)]
                    (-/or (get (get (? this :fun) :regulars) n)
                        (-/let-when [fm (get (? this :fun) :variadic)] (-/and (some? fm) (<= (dec (- 0 (get fm :arity))) n)) => (Closure'throwArity this, (if (< n m) n (- 0 m)))
                            fm
                        )
                    )
                )
            #_"array" vars
                (let [
                    #_"int" m (inc (reduce max (inc -1) (-/map (λ [%] (get % :idx)) (-/vals (deref (get fm :'locals))))))
                    #_"int" n (get fm :arity) n (if (neg? n) (- 0 n) (inc n))
                ]
                    (-/loop-when-recur [vars (-/-> (anew m) (aset! 0 this)) #_"int" i 1 #_"seq" s (seq args)]
                                     (< i n)
                                     [(aset! vars i (first s)) (inc i) (next s)]
                                  => (if (some? s) (aset! vars i s) vars)
                    )
                )
        ]
            (Machine'compute (FnMethod''compile fm), vars)
        )
    ))
)
)

(-/about #_"beagle.Cons"

(-/about #_"Cons"
    (-/defq Cons [#_"Object" car, #_"seq" cdr]
        clojure.lang.ISeq (seq [_] (Cons''seq _)) (first [_] (Cons''first _)) (next [_] (Cons''next _)) (more [_] (-/or (Cons''next _) ()))
        clojure.lang.IPersistentCollection (count [_] (Cons''count _))
    )

    (def #_"Cons" Cons'new (λ [#_"Object" car, #_"seq" cdr]
        (-/new* Cons'class (anew [car, cdr]))
    ))

    (def #_"Cons" Cons'nil (Cons'new nil, nil))

    (def #_"seq" Cons''seq (λ [#_"Cons" this]
        (-/when-not (identical? this Cons'nil) => nil
            this
        )
    ))

    (def #_"Object" Cons''first (λ [#_"Cons" this]
        (? this :car)
    ))

    (def #_"seq" Cons''next (λ [#_"Cons" this]
        (seq (? this :cdr))
    ))

    (def #_"int" Cons''count (λ [#_"Cons" this]
        (-/when-not (identical? this Cons'nil) => 0
            (inc (count (? this :cdr)))
        )
    ))

    (def #_"boolean" Cons''equals (λ [#_"Cons" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (seqable? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))
)

(def cons (λ [x s] (Cons'new x, (seq s))))

(def spread (λ [s]
    (-/cond
        (nil? s) nil
        (nil? (next s)) (seq (first s))
        :else (cons (first s) (spread (next s)))
    )
))

(def reverse (λ [s] (reduce (λ [%1 %2] (cons %2 %1)) Cons'nil s)))

(def list (λ [& s] (if (some? s) (reverse (reverse s)) Cons'nil)))
)

(-/about #_"beagle.PersistentMap"

(-/about #_"MSeq"
    (-/defq MSeq [#_"array" a, #_"int" i]
        clojure.lang.ISeq (seq [_] (MSeq''seq _)) (first [_] (MSeq''first _)) (next [_] (MSeq''next _)) (more [_] (-/or (MSeq''next _) ()))
    )

    (def #_"MSeq" MSeq'new (λ [#_"array" a, #_"int" i]
        (-/new* MSeq'class (anew [a, i]))
    ))

    (def #_"seq" MSeq''seq (λ [#_"MSeq" this]
        this
    ))

    (def #_"pair" MSeq''first (λ [#_"MSeq" this]
        (list (aget (? this :a) (? this :i)) (aget (? this :a) (inc (? this :i))))
    ))

    (def #_"seq" MSeq''next (λ [#_"MSeq" this]
        (-/when (< (+ (? this :i) 2) (alength (? this :a)))
            (MSeq'new (? this :a), (+ (? this :i) 2))
        )
    ))

    (def #_"int" MSeq''count (λ [#_"MSeq" this]
        (>> (- (alength (? this :a)) (? this :i)) 1)
    ))

    (def #_"boolean" MSeq''equals (λ [#_"MSeq" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (seqable? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))
)

(-/about #_"PersistentMap"
    (-/declare PersistentMap''assoc PersistentMap''containsKey)

    (-/defq PersistentMap [#_"array" array]
        clojure.lang.Associative (assoc [_, key, val] (PersistentMap''assoc _, key, val)) (containsKey [_, key] (PersistentMap''containsKey _, key))
    )

    (def #_"PersistentMap" PersistentMap'new (λ [#_"array" a]
        (-/new* PersistentMap'class (anew [(-/or a (anew 0))]))
    ))

    (def #_"PersistentMap" PersistentMap'EMPTY (PersistentMap'new nil))

    (def #_"PersistentMap" PersistentMap'create (λ [#_"array" a]
        (if (-/and (some? a) (pos? (alength a))) (PersistentMap'new a) PersistentMap'EMPTY)
    ))

    (def #_"int" PersistentMap''count (λ [#_"PersistentMap" this]
        (>> (alength (? this :array)) 1)
    ))

    (def #_"int" PersistentMap'index-of (λ [#_"array" a, #_"key" key]
        (-/loop-when [#_"int" i 0] (< i (alength a)) => -1
            (if (= (aget a i) key) i (recur (+ i 2)))
        )
    ))

    (def #_"value" PersistentMap''valAt (λ [#_"PersistentMap" this, #_"key" key]
        (let [
            #_"array" a (? this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (-/when (< -1 i)
                (aget a (inc i))
            )
        )
    ))

    (def #_"PersistentMap" PersistentMap''assoc (λ [#_"PersistentMap" this, #_"key" key, #_"value" val]
        (let [
            #_"array" a (? this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (if (< -1 i)
                (if (= (aget a (inc i)) val)
                    this
                    (PersistentMap'new (-/-> (aclone a) (aset! (inc i) val)))
                )
                (let [
                    #_"int" n (alength a)
                    #_"array" a' (anew (+ n 2))
                    a' (if (pos? n) (acopy! a' 0 a 0 n) a')
                ]
                    (PersistentMap'new (-/-> a' (aset! n key) (aset! (inc n) val)))
                )
            )
        )
    ))

    (def #_"boolean" PersistentMap''containsKey (λ [#_"PersistentMap" this, #_"key" key]
        (< -1 (PersistentMap'index-of (? this :array), key))
    ))

    (def #_"PersistentMap" PersistentMap''dissoc (λ [#_"PersistentMap" this, #_"key" key]
        (let [
            #_"array" a (? this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (-/when (< -1 i) => this
                (-/let-when [#_"int" n (- (alength a) 2)] (pos? n) => PersistentMap'EMPTY
                    (let [
                        #_"array" a' (-/-> (anew n) (acopy! 0 a 0 i) (acopy! i a (+ i 2) (- n i)))
                    ]
                        (PersistentMap'new a')
                    )
                )
            )
        )
    ))

    (def #_"seq" PersistentMap''seq (λ [#_"PersistentMap" this]
        (-/when (pos? (alength (? this :array)))
            (MSeq'new (? this :array), 0)
        )
    ))

    (-/declare contains?)

    (def #_"boolean" PersistentMap''equals (λ [#_"PersistentMap" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (map? that) (= (count that) (count this))
                (-/loop-when [#_"seq" s (seq this)] (some? s) => true
                    (let [#_"pair" e (first s) #_"Object" k (first e)]
                        (-/and (contains? that k) (= (second e) (get that k))
                            (recur (next s))
                        )
                    )
                )
            )
        )
    ))
)

(def assoc (λ [m k v]
    (-/cond
        (nil? m)                       (PersistentMap'new (anew [k, v]))
        (-/satisfies? PersistentMap m) (PersistentMap''assoc m, k, v)
        (-/clojure-associative? m)     (-/Associative''assoc m, k, v)
        :else                          (-/throw! (str "assoc not supported on " m))
    )
))

(def dissoc (λ [m k]
    (-/cond
        (nil? m)                       nil
        (-/satisfies? PersistentMap m) (PersistentMap''dissoc m, k)
        (-/clojure-map? m)             (-/IPersistentMap''dissoc m, k)
        :else                          (-/throw! (str "dissoc not supported on " m))
    )
))

(def array-map (λ [& kvs] (if (some? kvs) (reduce-kv assoc PersistentMap'EMPTY kvs) PersistentMap'EMPTY)))

(def contains? (λ [m k]
    (-/cond
        (nil? m)                       false
        (-/satisfies? PersistentMap m) (PersistentMap''containsKey m, k)
        (-/clojure-associative? m)     (-/Associative''containsKey m, k)
        :else                          (-/throw! (str "contains? not supported on " m))
    )
))

(def get (λ [m k]
    (-/cond
        (nil? m)                       nil
        (-/satisfies? PersistentMap m) (PersistentMap''valAt m, k)
        (-/clojure-ilookup? m)         (-/ILookup''valAt m, k)
        :else                          (-/throw! (str "get not supported on " m))
    )
))

(def update (λ [m k f] (assoc m k (f (get m k)))))
)

(-/about #_"beagle.Var"

(-/about #_"Var"
    (def #_"Var" Var'new (λ []
        (atom nil)
    ))

    (def #_"Object" Var''get (λ [#_"Var" this]
        (-/when-not (-/clojure-var? this) => (-/Var''-get this)
            (deref this)
        )
    ))

    (def #_"void" Var''bindRoot (λ [#_"Var" this, #_"Object" root]
        (reset! this root)
        nil
    ))
)
)

(-/about #_"beagle.Machine"

(-/about #_"Machine"
    (def #_"Object" Machine'compute (λ [#_"code" code, #_"array" vars]
        (loop [#_"stack" s nil #_"int" i 0]
            (let [xy (-/nth code i) x (first xy) y (second xy)]
                (-/cond
                    (= x :anew)     (let [a (first s)                          s (next s)]                  (recur (cons (anew a) s)                  (inc i)))
                    (= x :apply)    (let [b (first s) a (second s)             s (next s)]                  (recur (cons (apply a b) s)               (inc i)))
                    (= x :aset)     (let [c (first s) b (second s) a (third s) s (next s)] (aset! a b c)    (recur s                                  (inc i)))
                    (= x :create)   (let [a (first s)                          s (next s)]                  (recur (cons (Closure'new y, a) s)        (inc i)))
                    (= x :dup)      (let [a (first s)]                                                      (recur (cons a s)                         (inc i)))
                    (= x :get)      (let [a (first s)                          s (next s)]                  (recur (cons (get (deref (get a :_env)) y) s) (inc i)))
                    (= x :goto)                                                                             (recur s                        (deref y))
                    (= x :if-eq?)   (let [b (first s) a (second s)             s (next s)]                  (recur s        (if     (= a b) (deref y) (inc i))))
                    (= x :if-nil?)  (let [a (first s)                          s (next s)]                  (recur s        (if  (nil? a)   (deref y) (inc i))))
                    (= x :invoke-1) (let [a (first s)                          s (next s)]                  (recur (cons (y a) s)                     (inc i)))
                    (= x :invoke-2) (let [b (first s) a (second s)             s (next s)]                  (recur (cons (y a b) s)                   (inc i)))
                    (= x :load)                                                                             (recur (cons (aget vars y) s)             (inc i))
                    (= x :pop)                                                                              (recur (next s)                           (inc i))
                    (= x :push)                                                                             (recur (cons y s)                         (inc i))
                    (= x :return)                                                                                  (first s)
                    (= x :store)    (let [a (first s)                          s (next s)] (aset! vars y a) (recur s                                  (inc i)))
                    :else                                                                                   (-/throw! "oops!")
                )
            )
        )
    ))
)
)

(-/about #_"beagle.Compiler"

(-/about #_"asm"
    (def #_"gen" Gen'new (λ [] nil))

    (def #_"label" Gen''label (λ [#_"gen" gen] (atom nil)))

    (def #_"label" Gen''mark (λ [#_"gen" gen] (atom (count gen))))

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
    (def #_"gen" Gen''load     (λ [#_"gen" gen, #_"int" index]   (cons [:load index] gen)))
    (def #_"gen" Gen''pop      (λ [#_"gen" gen]                  (cons [:pop] gen)))
    (def #_"gen" Gen''push     (λ [#_"gen" gen, #_"value" value] (cons [:push value] gen)))
    (def #_"gen" Gen''return   (λ [#_"gen" gen]                  (cons [:return] gen)))
    (def #_"gen" Gen''store    (λ [#_"gen" gen, #_"int" index]   (cons [:store index] gen)))
)

(-/about #_"Compiler"
    (def #_"int" Compiler'MAX_POSITIONAL_ARITY #_9 (+ 9 2))

    (-/declare Expr''emit)

    (def #_"gen" Compiler'emitArgs (λ [#_"map" scope, #_"gen" gen, #_"Expr*" args]
        (let [
            gen (Gen''push gen, (count args))
            gen (Gen''anew gen)
        ]
            (-/loop-when [gen gen #_"int" i 0 #_"seq" s (seq args)] (some? s) => gen
                (let [
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (Expr''emit (first s), :Context'EXPRESSION, scope, gen)
                    gen (Gen''aset gen)
                ]
                    (recur gen (inc i) (next s))
                )
            )
        )
    ))

    (-/declare FnMethod''emitLocal)

    (def #_"gen" Compiler'emitLocals (λ [#_"map" scope, #_"gen" gen, #_"map" locals]
        (let [
            gen (Gen''push gen, (<< (count locals) 1))
            gen (Gen''anew gen)
        ]
            (-/loop-when [gen gen #_"int" i 0 #_"seq" s (-/vals locals)] (some? s) => gen
                (let [
                    #_"LocalBinding" lb (first s)
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (Gen''push gen, (get lb :sym))
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
    ))
)

(-/about #_"LiteralExpr"
    (def #_"LiteralExpr" LiteralExpr'new (λ [#_"Object" value]
        (array-map
            #_"keyword" :class :LiteralExpr'class
            #_"Object" :value value
        )
    ))

    (def #_"LiteralExpr" LiteralExpr'NIL   (LiteralExpr'new nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (LiteralExpr'new true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (LiteralExpr'new false))

    (def #_"Expr" LiteralExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (dec (count form))]
            (-/when (= n 1) => (-/throw! (str "wrong number of arguments passed to quote: " n))
                (let [#_"Object" x (second form)]
                    (-/cond
                        (= x nil)    LiteralExpr'NIL
                        (= x true)   LiteralExpr'TRUE
                        (= x false)  LiteralExpr'FALSE
                        :else       (LiteralExpr'new x)
                    )
                )
            )
        )
    ))

    (def #_"gen" LiteralExpr''emit (λ [#_"LiteralExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-not (= context :Context'STATEMENT) => gen
            (Gen''push gen, (get this :value))
        )
    ))
)

(-/about #_"VarExpr"
    (def #_"VarExpr" VarExpr'new (λ [#_"Var" var]
        (array-map
            #_"keyword" :class :VarExpr'class
            #_"Var" :var var
        )
    ))

    (def #_"gen" VarExpr''emit (λ [#_"VarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (get this :var))
            gen (Gen''invoke-1 gen, Var''get)
        ]
            (-/when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    ))
)

(-/about #_"BodyExpr"
    (def #_"BodyExpr" BodyExpr'new (λ [#_"Expr*" exprs]
        (array-map
            #_"keyword" :class :BodyExpr'class
            #_"Expr*" :exprs exprs
        )
    ))

    (-/declare Compiler'analyze)

    (def #_"Expr" BodyExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"seq" s form s (if (= (first s) 'do) (next s) s)
              #_"Expr*" z
                (-/loop-when [z nil s s] (some? s) => (reverse z)
                    (let [#_"Context" c (if (-/or (= context :Context'STATEMENT) (some? (next s))) :Context'STATEMENT context)]
                        (recur (cons (Compiler'analyze (first s), c, scope) z) (next s))
                    )
                )]
            (BodyExpr'new (-/or (seq z) (list LiteralExpr'NIL)))
        )
    ))

    (def #_"gen" BodyExpr''emit (λ [#_"BodyExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/loop-when-recur [gen gen #_"seq" s (seq (get this :exprs))]
                         (some? (next s))
                         [(Expr''emit (first s), :Context'STATEMENT, scope, gen) (next s)]
                      => (Expr''emit (first s), context, scope, gen)
        )
    ))
)

(-/about #_"IfExpr"
    (def #_"IfExpr" IfExpr'new (λ [#_"Expr" test, #_"Expr" then, #_"Expr" else]
        (array-map
            #_"keyword" :class :IfExpr'class
            #_"Expr" :test test
            #_"Expr" :then then
            #_"Expr" :else else
        )
    ))

    (def #_"Expr" IfExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/cond
            (< 4 (count form)) (-/throw! "too many arguments to if")
            (< (count form) 3) (-/throw! "too few arguments to if")
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

(-/about #_"InvokeExpr"
    (def #_"InvokeExpr" InvokeExpr'new (λ [#_"Expr" fexpr, #_"Expr*" args]
        (array-map
            #_"keyword" :class :InvokeExpr'class
            #_"Expr" :fexpr fexpr
            #_"Expr*" :args args
        )
    ))

    (def #_"Expr" InvokeExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"Expr" fexpr (Compiler'analyze (first form), :Context'EXPRESSION, scope)
            #_"Expr*" args (-/doall (-/map (λ [%] (Compiler'analyze %, :Context'EXPRESSION, scope)) (next form)))
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
            (-/when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    ))
)

(let [last-uid' (atom 0)] (def next-uid! (λ [] (swap! last-uid' inc))))

(-/about #_"LocalBinding"
    (def #_"LocalBinding" LocalBinding'new (λ [#_"Symbol" sym, #_"Expr" init, #_"int" idx]
            (array-map
                 #_"int" :uid (next-uid!)
                 #_"Symbol" :sym sym
                 #_"Expr'" :'init (atom init)
                 #_"int" :idx idx
            )
    ))
)

(-/about #_"LocalBindingExpr"
    (def #_"LocalBindingExpr" LocalBindingExpr'new (λ [#_"LocalBinding" lb]
        (array-map
            #_"keyword" :class :LocalBindingExpr'class
            #_"LocalBinding" :lb lb
        )
    ))

    (def #_"gen" LocalBindingExpr''emit (λ [#_"LocalBindingExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-not (= context :Context'STATEMENT) => gen
            (FnMethod''emitLocal (get scope :fm), gen, (get this :lb))
        )
    ))
)

(-/about #_"FnMethod"
    (def #_"FnMethod" FnMethod'new (λ [#_"FnExpr" fun, #_"FnMethod" parent]
        (array-map
            #_"FnExpr" :fun fun
            #_"FnMethod" :parent parent
            #_"{int LocalBinding}'" :'locals (atom (-/array-map))
            #_"Integer" :arity nil
            #_"Expr" :body nil
        )
    ))

    (def #_"FnMethod" FnMethod'parse (λ [#_"FnExpr" fun, #_"seq" form, #_"map" scope]
        (let [
            scope (update scope :fm (λ [%] (FnMethod'new fun %)))
            scope (update scope :'local-env (comp atom deref))
            scope (assoc scope :'local-num (atom 0))
            _
                (-/when-some [#_"Symbol" f (get fun :fname)]
                    (let [#_"LocalBinding" lb (LocalBinding'new f, nil, (deref (get scope :'local-num)))]
                        (swap! (get scope :'local-env) assoc (get lb :sym) lb)
                        (swap! (get (get scope :fm) :'locals) assoc (get lb :uid) lb)
                    )
                )
            _
                (-/loop-when [lbs nil arity 0 #_"boolean" variadic? false #_"seq" s (seq (first form))] (some? s) => (if (-/and variadic? (not (neg? arity))) (-/throw! "missing variadic parameter") [(reverse lbs) arity])
                    (let [#_"symbol?" sym (first s)]
                        (-/when (symbol? sym)        => (-/throw! "function parameters must be symbols")
                            (-/when (nil? (? sym :ns)) => (-/throw! (str "can't use qualified name as parameter: " sym))
                                (-/cond
                                    (= sym '&)
                                        (-/when-not variadic? => (-/throw! "overkill variadic parameter list")
                                            (recur lbs arity true (next s))
                                        )
                                    (neg? arity)
                                        (-/throw! (str "excess variadic parameter: " sym))
                                    ((if variadic? <= <) arity Compiler'MAX_POSITIONAL_ARITY)
                                        (let [
                                            arity (-/if-not variadic? (inc arity) (- 0 (inc arity)))
                                            #_"LocalBinding" lb (LocalBinding'new sym, nil, (swap! (get scope :'local-num) inc))
                                        ]
                                            (swap! (get scope :'local-env) assoc (get lb :sym) lb)
                                            (swap! (get (get scope :fm) :'locals) assoc (get lb :uid) lb)
                                            (recur (cons lb lbs) arity variadic? (next s))
                                        )
                                    :else
                                        (-/throw! (str "can't specify more than " Compiler'MAX_POSITIONAL_ARITY " positional parameters"))
                                )
                            )
                        )
                    )
                )
            #_"LocalBinding*" lbs (first _) #_"int" arity (second _)
            scope (assoc scope :loop-locals lbs)
            scope (update scope :fm (λ [%] (assoc % :arity arity)))
        ]
            (assoc (get scope :fm) :body (BodyExpr'parse (next form), :Context'RETURN, scope))
        )
    ))

    (def #_"gen" FnMethod''emitLocal (λ [#_"FnMethod" this, #_"gen" gen, #_"LocalBinding" lb]
        (if (contains? (deref (get (get this :fun) :'closes)) (get lb :uid))
            (let [
                gen (Gen''load gen, 0)
                gen (Gen''get gen, (get lb :sym))
            ]
                gen
            )
            (Gen''load gen, (get lb :idx))
        )
    ))

    (def #_"code" FnMethod''compile (λ [#_"FnMethod" this]
        (let [
            #_"map" scope (array-map :fm this)
            #_"gen" gen (Gen'new)
            scope (assoc scope :loop-label (Gen''mark gen))
            gen (Expr''emit (get this :body), :Context'RETURN, scope, gen)
            gen (Gen''return gen)
        ]
            (-/vec (reverse gen))
        )
    ))
)

(-/about #_"FnExpr"
    (def #_"FnExpr" FnExpr'new (λ []
        (array-map
            #_"keyword" :class :FnExpr'class
            #_"Symbol" :fname nil
            #_"{int FnMethod}" :regulars nil
            #_"FnMethod" :variadic nil
            #_"{int LocalBinding}'" :'closes (atom (-/array-map))
        )
    ))

    (def #_"FnExpr" FnExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [
            #_"FnExpr" fun (FnExpr'new)
            _
                (-/when (symbol? (second form)) => [fun form]
                    [(assoc fun :fname (second form)) (cons (symbol! 'λ) (next (next form)))]
                )
            fun (first _) form (second _)
            form
                (-/when (-/vector? (second form)) => form
                    (list (symbol! 'λ) (next form))
                )
            _
                (-/loop-when [regulars (array-map) variadic nil #_"seq" s (next form)] (some? s) => [regulars variadic]
                    (let [#_"FnMethod" fm (FnMethod'parse fun, (first s), scope) #_"int" n (get fm :arity)]
                        (if (neg? n)
                            (-/when (nil? variadic) => (-/throw! "can't have more than 1 variadic overload")
                                (recur regulars fm (next s))
                            )
                            (-/when (nil? (get regulars n)) => (-/throw! "can't have 2 overloads with same arity")
                                (recur (assoc regulars n fm) variadic (next s))
                            )
                        )
                    )
                )
            #_"{int FnMethod}" regulars (first _) #_"FnMethod" variadic (second _)
        ]
            (-/when (some? variadic)
                (-/loop-when-recur [#_"int" n (- 0 (get variadic :arity))] (<= n Compiler'MAX_POSITIONAL_ARITY) [(inc n)]
                    (-/when (some? (get regulars n))
                        (-/throw! "can't have fixed arity function with more params than variadic function")
                    )
                )
            )
            (-/-> fun (assoc :regulars regulars) (assoc :variadic variadic))
        )
    ))

    (def #_"gen" FnExpr''emit (λ [#_"FnExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-not (= context :Context'STATEMENT) => gen
            (let [
                gen (Compiler'emitLocals scope, gen, (deref (get this :'closes)))
                gen (Gen''invoke-1 gen, PersistentMap'create)
            ]
                (Gen''create gen, this)
            )
        )
    ))
)

(-/about #_"DefExpr"
    (def #_"DefExpr" DefExpr'new (λ [#_"Var" var, #_"Expr" init, #_"boolean" initProvided]
        (array-map
            #_"keyword" :class :DefExpr'class
            #_"Var" :var var
            #_"Expr" :init init
            #_"boolean" :initProvided initProvided
        )
    ))

    (def #_"{Symbol Var}'" Beagle'ns (atom (array-map)))

    (def #_"Var" DefExpr'lookupVar (λ [#_"Symbol" sym]
        (let [sym (symbol! sym)]
            (-/when (nil? (? sym :ns)) => (-/throw! "can't create defs outside of current ns")
                (-/or
                    (get (deref Beagle'ns) sym)
                    (let [#_"var" v (Var'new)]
                        (swap! Beagle'ns assoc sym v)
                        v
                    )
                )
            )
        )
    ))

    (def #_"Expr" DefExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"int" n (count form)]
            (-/cond
                (< 3 n) (-/throw! "too many arguments to def")
                (< n 2) (-/throw! "too few arguments to def")
                :else
                    (-/let-when [#_"symbol?" s (second form)] (symbol? s) => (-/throw! "first argument to def must be a symbol")
                        (DefExpr'new (DefExpr'lookupVar s), (Compiler'analyze (third form), :Context'EXPRESSION, scope), (= n 3))
                    )
            )
        )
    ))

    (def #_"gen" DefExpr''emit (λ [#_"DefExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen (Gen''push gen, (get this :var))
            gen
                (-/when (get this :initProvided) => gen
                    (let [
                        gen (Gen''dup gen)
                        gen (Expr''emit (get this :init), :Context'EXPRESSION, scope, gen)
                        gen (Gen''invoke-2 gen, Var''bindRoot)
                    ]
                        (Gen''pop gen)
                    )
                )
        ]
            (-/when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    ))
)

(-/about #_"LetExpr"
    (def #_"LetExpr" LetExpr'new (λ [#_"LocalBinding*" bindings, #_"Expr" body, #_"boolean" loop?]
        (array-map
            #_"keyword" :class :LetExpr'class
            #_"LocalBinding*" :bindings bindings
            #_"Expr" :body body
            #_"boolean" :loop? loop?
        )
    ))

    (def #_"Expr" LetExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (let [#_"vector?" bindings (second form)]
            (-/when (-/vector? bindings)                 => (-/throw! "bad binding form, expected vector")
                (-/when (zero? (& (count bindings) 1)) => (-/throw! "bad binding form, expected matched symbol expression pairs")
                    (let [
                        scope (update scope :'local-env (comp atom deref))
                        scope (update scope :'local-num (comp atom deref))
                        #_"boolean" loop? (-/or (= (first form) 'loop) (= (first form) 'loop*))
                        scope
                            (-/when loop? => scope
                                (dissoc scope :loop-locals)
                            )
                        #_"LocalBinding*" lbs
                            (-/loop-when [lbs nil #_"seq" s (seq bindings)] (some? s) => (reverse lbs)
                                (let [#_"symbol?" sym (first s)]
                                    (-/when (symbol? sym)        => (-/throw! (str "bad binding form, expected symbol, got: " sym))
                                        (let [sym (symbol! sym)]
                                            (-/when (nil? (? sym :ns)) => (-/throw! (str "can't let qualified name: " sym))
                                                (let [
                                                    #_"Expr" init (Compiler'analyze (second s), :Context'EXPRESSION, scope)
                                                    #_"LocalBinding" lb (LocalBinding'new sym, init, (swap! (get scope :'local-num) inc))
                                                ]
                                                    (swap! (get scope :'local-env) assoc (get lb :sym) lb)
                                                    (swap! (get (get scope :fm) :'locals) assoc (get lb :uid) lb)
                                                    (recur (cons lb lbs) (next (next s)))
                                                )
                                            )
                                        )
                                    )
                                )
                            )
                        scope
                            (-/when loop? => scope
                                (assoc scope :loop-locals lbs)
                            )
                        #_"Expr" body (BodyExpr'parse (next (next form)), (if loop? :Context'RETURN context), scope)
                    ]
                        (LetExpr'new lbs, body, loop?)
                    )
                )
            )
        )
    ))

    (def #_"gen" LetExpr''emit (λ [#_"LetExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [
            gen
                (-/loop-when [gen gen #_"seq" s (seq (get this :bindings))] (some? s) => gen
                    (let [
                        #_"LocalBinding" lb (first s)
                        gen (Expr''emit (deref (get lb :'init)), :Context'EXPRESSION, scope, gen)
                        gen (Gen''store gen, (get lb :idx))
                    ]
                        (recur gen (next s))
                    )
                )
            scope
                (-/when (get this :loop?) => scope
                    (assoc scope :loop-label (Gen''mark gen))
                )
        ]
            (Expr''emit (get this :body), context, scope, gen)
        )
    ))
)

(-/about #_"RecurExpr"
    (def #_"RecurExpr" RecurExpr'new (λ [#_"LocalBinding*" loopLocals, #_"Expr*" args]
        (array-map
            #_"keyword" :class :RecurExpr'class
            #_"LocalBinding*" :loopLocals loopLocals
            #_"Expr*" :args args
        )
    ))

    (def #_"Expr" RecurExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/when (-/and (= context :Context'RETURN) (contains? scope :loop-locals)) => (-/throw! "can only recur from tail position")
            (let [#_"Expr*" args (-/doall (-/map (λ [%] (Compiler'analyze %, :Context'EXPRESSION, scope)) (next form))) #_"int" n (count args) #_"int" m (count (get scope :loop-locals))]
                (-/when (= n m) => (-/throw! (str "mismatched argument count to recur, expected: " m " args, got: " n))
                    (RecurExpr'new (get scope :loop-locals), args)
                )
            )
        )
    ))

    (def #_"gen" RecurExpr''emit (λ [#_"RecurExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-some [#_"label" l'loop (get scope :loop-label)] => (-/throw! "recur misses loop label")
            (let [
                gen
                    (-/loop-when-recur [gen gen #_"seq" s (seq (get this :args))]
                                     (some? s)
                                     [(Expr''emit (first s), :Context'EXPRESSION, scope, gen) (next s)]
                                  => gen
                    )
                gen
                    (-/loop-when-recur [gen gen #_"seq" s (reverse (get this :loopLocals))]
                                     (some? s)
                                     [(Gen''store gen, (get (first s) :idx)) (next s)]
                                  => gen
                    )
            ]
                (Gen''goto gen, l'loop)
            )
        )
    ))
)

(-/about #_"Expr"
    (def #_"gen" Expr''emit (λ [#_"Expr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (let [#_"keyword" k (get this :class)]
            (-/cond
                (= k :LiteralExpr'class)      (LiteralExpr''emit this, context, scope, gen)
                (= k :VarExpr'class)          (VarExpr''emit this, context, scope, gen)
                (= k :BodyExpr'class)         (BodyExpr''emit this, context, scope, gen)
                (= k :IfExpr'class)           (IfExpr''emit this, context, scope, gen)
                (= k :InvokeExpr'class)       (InvokeExpr''emit this, context, scope, gen)
                (= k :LocalBindingExpr'class) (LocalBindingExpr''emit this, context, scope, gen)
                (= k :FnExpr'class)           (FnExpr''emit this, context, scope, gen)
                (= k :DefExpr'class)          (DefExpr''emit this, context, scope, gen)
                (= k :LetExpr'class)          (LetExpr''emit this, context, scope, gen)
                (= k :RecurExpr'class)        (RecurExpr''emit this, context, scope, gen)
                :else                         (-/throw! (str "Expr''emit not supported on " this))
            )
        )
    ))
)

(-/about #_"Compiler"
    (def #_"map" Compiler'specials
        (array-map
            '&          nil
            'def        DefExpr'parse
            'do         BodyExpr'parse
            'λ          FnExpr'parse
            'if         IfExpr'parse
            'let        LetExpr'parse            'let*       LetExpr'parse
            'loop       LetExpr'parse            'loop*      LetExpr'parse
            'quote      LiteralExpr'parse
            'recur      RecurExpr'parse
        )
    )

    (def #_"void" Compiler'closeOver (λ [#_"LocalBinding" lb, #_"FnMethod" fm]
        (-/when (-/and (some? lb) (some? fm) (not (contains? (deref (get fm :'locals)) (get lb :uid))))
            (swap! (get (get fm :fun) :'closes) assoc (get lb :uid) lb)
            (Compiler'closeOver lb, (get fm :parent))
        )
        nil
    ))

    (def #_"Expr" Compiler'analyzeSymbol (λ [#_"Symbol" sym, #_"map" scope]
        (let [sym (symbol! sym)]
            (-/or
                (-/when (= (-/String''charAt (? sym :name), 0) \:)
                    (LiteralExpr'new sym)
                )
                (-/when (nil? (? sym :ns))
                    (-/when-some [#_"LocalBinding" lb (get (deref (get scope :'local-env)) sym)]
                        (Compiler'closeOver lb, (get scope :fm))
                        (LocalBindingExpr'new lb)
                    )
                )
                (let [#_"Object" o
                        (if (some? (? sym :ns))
                            (-/Namespace''findInternedVar (-/the-ns 'beagle.core), (-/symbol (? sym :name)))
                            (get (deref Beagle'ns) sym)
                        )]
                    (-/when (some? o) => (-/throw! (str "unable to resolve symbol: " sym " in this context"))
                        (VarExpr'new o)
                    )
                )
            )
        )
    ))

    (def #_"Expr" Compiler'analyzeSeq (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/when-some [#_"Object" op (first form)] => (-/throw! (str "can't call nil, form: " form))
            (let [#_"fn" f'parse (-/or (get Compiler'specials op) InvokeExpr'parse)]
                (f'parse form, context, scope)
            )
        )
    ))

    (def #_"Expr" Compiler'analyze (λ [#_"edn" form, #_"Context" context, #_"map" scope]
        (-/cond
            (= form nil)                    LiteralExpr'NIL
            (= form true)                   LiteralExpr'TRUE
            (= form false)                  LiteralExpr'FALSE
            (symbol? form)                 (Compiler'analyzeSymbol form, scope)
            (-/and (seq? form) (seq form)) (Compiler'analyzeSeq form, context, scope)
            :else                          (LiteralExpr'new form)
        )
    ))

    (def #_"edn" Compiler'eval (λ [#_"edn" form, #_"map" scope]
        (apply (Closure'new (Compiler'analyze (list (symbol! 'λ) [] form), :Context'EXPRESSION, scope), nil))
    ))
)
)

(-/about #_"beagle.LispReader"

(-/about #_"LispReader"
    (-/declare LispReader'macros)

    (def #_"boolean" LispReader'isMacro (λ [#_"char" ch]
        (contains? LispReader'macros ch)
    ))

    (def #_"boolean" LispReader'isTerminatingMacro (λ [#_"char" ch]
        (-/and (LispReader'isMacro ch) (not= ch \#) (not= ch \'))
    ))

    (def #_"boolean" LispReader'isDigit (λ [#_"char" ch, #_"int" base]
        (not= (-/Character'digit ch, base) -1)
    ))

    (def #_"boolean" LispReader'isWhitespace (λ [#_"char" ch]
        (-/or (-/Character'isWhitespace ch) (= ch \,))
    ))

    (def #_"Character" LispReader'read1 (λ [#_"Reader" r]
        (let [#_"int" c (-/Reader''read r)]
            (-/when-not (= c -1)
                (-/char c)
            )
        )
    ))

    (def #_"void" LispReader'unread (λ [#_"PushbackReader" r, #_"Character" ch]
        (-/when (some? ch)
            (-/PushbackReader''unread r, (-/int ch))
        )
        nil
    ))

    (def #_"Pattern" LispReader'rxInteger (-/Pattern'compile "[-+]?(?:0|[1-9][0-9]*)"))

    (def #_"Object" LispReader'matchNumber (λ [#_"String" s]
        (-/let-when [#_"Matcher" m (-/Pattern''matcher LispReader'rxInteger, s)] (-/Matcher''matches m)
            (-/Integer'parseInt s)
        )
    ))

    (def #_"Object" LispReader'readNumber (λ [#_"PushbackReader" r, #_"char" ch]
        (let [#_"String" s
                (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, ch)]
                    (loop []
                        (let [ch (LispReader'read1 r)]
                            (if (-/or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isMacro ch))
                                (do
                                    (LispReader'unread r, ch)
                                    (-/StringBuilder''toString sb)
                                )
                                (do
                                    (-/StringBuilder''append sb, ch)
                                    (recur)
                                )
                            )
                        )
                    )
                )]
            (-/or (LispReader'matchNumber s) (-/throw! (str "invalid number: " s)))
        )
    ))

    (def #_"String" LispReader'readToken (λ [#_"PushbackReader" r, #_"char" ch]
        (let [#_"StringBuilder" sb (-/StringBuilder'new) _ (-/StringBuilder''append sb, ch)]
            (loop []
                (let [ch (LispReader'read1 r)]
                    (if (-/or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isTerminatingMacro ch))
                        (do
                            (LispReader'unread r, ch)
                            (-/StringBuilder''toString sb)
                        )
                        (do
                            (-/StringBuilder''append sb, ch)
                            (recur)
                        )
                    )
                )
            )
        )
    ))

    (def #_"Pattern" LispReader'rxSymbol (-/Pattern'compile "(?:-/)?[-+:a-zA-Z_*?!<=>&%λ][-+:a-zA-Z_*?!<=>&%0-9'#]*"))

    (def #_"Object" LispReader'matchSymbol (λ [#_"String" s]
        (-/let-when [#_"Matcher" m (-/Pattern''matcher LispReader'rxSymbol, s)] (-/Matcher''matches m)
            (symbol s)
        )
    ))

    (def #_"Object" LispReader'interpretToken (λ [#_"String" s]
        (-/cond (= s "nil") nil (= s "true") true (= s "false") false :else
            (-/or (LispReader'matchSymbol s) (-/throw! (str "invalid token: " s)))
        )
    ))

    (def #_"Object" LispReader'read (λ [#_"PushbackReader" r, #_"map" scope, #_"Character" delim]
        (loop []
            (let [#_"char" ch (-/loop-when-recur [ch (LispReader'read1 r)] (-/and (some? ch) (LispReader'isWhitespace ch)) [(LispReader'read1 r)] => ch)]
                (-/cond
                    (nil? ch)
                        (-/throw! "EOF while reading")
                    (-/and (some? delim) (= delim ch))
                        delim
                    (LispReader'isDigit ch, 10)
                        (LispReader'readNumber r, ch)
                    :else
                        (let [#_"fn" f'macro (get LispReader'macros ch)]
                            (if (some? f'macro)
                                (let [#_"Object" o (f'macro r scope ch)]
                                    (-/recur-when (identical? o r) [] => o)
                                )
                                (-/or
                                    (-/when (-/or (= ch \+) (= ch \-))
                                        (let [#_"char" ch' (LispReader'read1 r) _ (LispReader'unread r, ch')]
                                            (-/when (-/and (some? ch') (LispReader'isDigit ch', 10))
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
    ))

    (def #_"seq" LispReader'readDelimitedForms (λ [#_"PushbackReader" r, #_"map" scope, #_"char" delim]
        (loop [#_"seq" z nil]
            (let [#_"Object" form (LispReader'read r, scope, delim)]
                (-/when (= form delim) => (recur (cons form z))
                    (reverse z)
                )
            )
        )
    ))

    (def #_"char" StringReader'escape (λ [#_"PushbackReader" r]
        (-/when-some [#_"char" ch (LispReader'read1 r)] => (-/throw! "EOF while reading string")
            (-/cond
                (= ch \n) \newline
                (= ch \\) ch
                (= ch \") ch ;; oops! "
                :else (-/throw! (str "unsupported escape character: \\" ch))
            )
        )
    ))

    (def #_"Object" string-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (let [#_"StringBuilder" sb (-/StringBuilder'new)]
            (loop []
                (-/when-some [#_"char" ch (LispReader'read1 r)] => (-/throw! "EOF while reading string")
                    (-/when-not (= ch \") ;; oops! "
                        (-/StringBuilder''append sb, (if (= ch \\) (StringReader'escape r) ch))
                        (recur)
                    )
                )
            )
            (-/StringBuilder''toString sb)
        )
    ))

    (def #_"Object" discard-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (LispReader'read r, scope, nil)
        r
    ))

    (def #_"Object" quote-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (list (symbol! 'quote) (LispReader'read r, scope, nil))
    ))

    (-/declare LispReader'dispatchMacros)

    (def #_"Object" dispatch-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (-/when-some [#_"char" ch (LispReader'read1 r)] => (-/throw! "EOF while reading character")
            (-/let-when [#_"fn" f'macro (get LispReader'dispatchMacros ch)] (nil? f'macro) => (f'macro r scope ch)
                (LispReader'unread r, ch)
                (-/throw! (str "no dispatch macro for: " ch))
            )
        )
    ))

    (def #_"Object" character-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (-/when-some [#_"char" ch (LispReader'read1 r)] => (-/throw! "EOF while reading character")
            (let [#_"String" token (LispReader'readToken r, ch)]
                (-/when-not (= (-/String''length token) 1) => (-/Character'valueOf (-/String''charAt token, 0))
                    (-/cond
                        (= token "newline") \newline
                        (= token "space")   \space
                        :else (-/throw! (str "unsupported character: \\" token))
                    )
                )
            )
        )
    ))

    (def #_"Object" list-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (apply list (LispReader'readDelimitedForms r, scope, \)))
    ))

    (def #_"Object" vector-reader (λ [#_"PushbackReader" r, #_"map" scope, #_"char" _delim]
        (-/vec (LispReader'readDelimitedForms r, scope, \]))
    ))

    (def #_"Object" unmatched-delimiter-reader (λ [#_"PushbackReader" _r, #_"map" scope, #_"char" delim]
        (-/throw! (str "unmatched delimiter: " delim))
    ))

    (def #_"{char fn}" LispReader'macros
        (array-map
            \"  string-reader ;; oops! "
            \'  quote-reader    \`  quote-reader
            \(  list-reader,    \)  unmatched-delimiter-reader
            \[  vector-reader,  \]  unmatched-delimiter-reader
            \\  character-reader
            \#  dispatch-reader
        )
    )

    (def #_"{char fn}" LispReader'dispatchMacros
        (array-map
            \_  discard-reader
        )
    )
)

(def read (λ [] (LispReader'read -/System'in, nil, nil)))
)

(-/about #_"Beagle"

(def repl (λ []
    (let [#_"map" scope (array-map :'local-env (atom (array-map)))]
        (loop []
            (print "\033[31mBeagle \033[32m=> \033[0m")
            (flush)
            (prn (Compiler'eval (read) scope))
            (recur)
        )
    )
))
)
