(ns beagle.core
    (:refer-clojure :only [])
)

(ns beagle.bore
    (:refer-clojure :only [*in* *ns* *out* aclone aget alength alter-var-root apply aset assoc assoc-in case class class? complement concat conj defn defn- defonce deref disj doseq drop drop-while eval every? find-protocol-method fn gensym import interleave keys keyword? list* map? mapcat merge meta munge namespace-munge ns-imports ns-resolve ns-unmap object-array partial partition range read-string resolve select-keys seq set some some? take-nth take-while vals var-get vary-meta with-meta zipmap])
    (:require [clojure.core :as -])
)

(-/defmacro import! [& syms-or-seqs] `(do (doseq [n# (keys (ns-imports *ns*))] (ns-unmap *ns* n#)) (import ~@syms-or-seqs)))

(import!
    [java.lang Appendable Character Class Error Integer Long Number Object String StringBuilder System]
    [java.lang.reflect Array Constructor]
    [java.io Flushable PrintWriter PushbackReader Reader]
    [java.util.regex Matcher Pattern]
    [clojure.lang Associative Counted DynamicClassLoader IHashEq ILookup IMeta IPersistentMap Keyword Namespace Seqable Var]
    [beagle.util.concurrent.atomic AtomicReference]
)

(-/defmacro refer! [ns s]
    (-/let [f (fn [%] (-/let [v (ns-resolve (-/the-ns (if (-/= ns '-) 'clojure.core ns)) %) n (vary-meta % merge (select-keys (meta v) [:macro]))] `(def ~n ~(var-get v))))]
        (if (-/symbol? s) (f s) (-/cons 'do (-/map f s)))
    )
)

(refer! - [< <= = == array-map atom bit-and bit-shift-left bit-shift-right boolean char cons defmacro defmethod extend-protocol first get identical? inc instance? int keyword let list loop map name namespace next ns-name nth print-method reduce satisfies? second seq? str symbol symbol? the-ns unchecked-add-int unchecked-dec-int unchecked-inc-int unchecked-subtract-int vec vector vector?])

(defmacro about [& s] (cons 'do s))

(defn throw! [#_"String" s] (throw (Error. s)))

(about #_"java.lang"

(about #_"Appendable"
    (defn #_"Appendable" Appendable''append [^Appendable this, #_"char|String" x] (.append this, x))
)

(about #_"Character"
    (defn char? [x] (instance? Character x))

    (defn #_"int"       Character'digit        [#_"char" ch, #_"int" radix] (Character/digit ch, radix))
    (defn #_"boolean"   Character'isWhitespace [#_"char" ch]                (Character/isWhitespace ch))
    (defn #_"Character" Character'valueOf      [#_"char" ch]                (Character/valueOf ch))
)

(about #_"Integer"
    (defn int? [x] (-/or (instance? Integer x) (instance? Long x)))

    (defn #_"int" Integer'parseInt [#_"String" s] (Integer/parseInt s))
)

(about #_"Number"
    (defn number? [x] (instance? Number x))

    (defn int! [^Number n] (.intValue n))

    (defn #_"String" Number''toString [^Number this] (.toString this))
)

(about #_"Object"
    (def Object'array (Class/forName "[Ljava.lang.Object;"))

    (defn #_"String" Object''toString [^Object this] (.toString this))
)

(about #_"String"
    (defn string? [x] (instance? String x))

    (defn #_"char"    String''charAt     [^String this, #_"int" i]    (.charAt this, i))
    (defn #_"boolean" String''endsWith   [^String this, #_"String" s] (.endsWith this, s))
    (defn #_"int"     String''indexOf   ([^String this, #_"int" ch]   (.indexOf this, ch))     ([^String this, #_"String" s, #_"int" from] (.indexOf this, s, from)))
    (defn #_"int"     String''length     [^String this]               (.length this))
    (defn #_"String"  String''substring ([^String this, #_"int" from] (.substring this, from)) ([^String this, #_"int" from, #_"int" over] (.substring this, from, over)))
)

(about #_"StringBuilder"
    (defn #_"StringBuilder" StringBuilder'new [] (StringBuilder.))

    (defn #_"StringBuilder" StringBuilder''append   [^StringBuilder this, #_"char" ch] (.append this, ch))
    (defn #_"String"        StringBuilder''toString [^StringBuilder this]              (.toString this))
)

(about #_"System"
    (defn #_"void" System'arraycopy [#_"array" a, #_"int" i, #_"array" b, #_"int" j, #_"int" n] (System/arraycopy a, i, b, j, n))

    (def System'in  *in*)
    (def System'out *out*)
)
)

(about #_"java.lang.reflect"

(about #_"Array"
    (defn array? [x] (.isArray (class x)))

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
    (defn #_"Pattern" Pattern'compile  [#_"String" s]                (Pattern/compile s))
    (defn #_"Matcher" Pattern''matcher [^Pattern this, #_"String" s] (.matcher this, s))
)

(about #_"Matcher"
    (defn #_"boolean" Matcher''matches [^Matcher this] (.matches this))
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
    (defn clojure-ilookup? [x] (instance? clojure.lang.ILookup x))

    (defn #_"value" ILookup''valAt ([^ILookup this, #_"key" key] (.valAt this, key)) ([^ILookup this, #_"key" key, #_"value" not-found] (.valAt this, key, not-found)))
)

(about #_"Keyword"
    (defn clojure-keyword? [x] (instance? clojure.lang.Keyword x))

    (defn #_"Symbol" Keyword''sym [^Keyword this] (.sym this))
)

(about #_"Namespace"
    (defn clojure-namespace? [x] (instance? clojure.lang.Namespace x))

    (defn #_"Object" Namespace''-getMapping      [^Namespace this, #_"Symbol" name] (.getMapping this, name))
    (defn #_"var"    Namespace''-intern          [^Namespace this, #_"Symbol" sym]  (.intern this, sym))
    (defn #_"var"    Namespace''-findInternedVar [^Namespace this, #_"Symbol" name] (.findInternedVar this, name))
)

(about #_"Symbol"
    (defn clojure-symbol? [x] (instance? clojure.lang.Symbol x))
)

(about #_"Var"
    (defn clojure-var? [x] (instance? clojure.lang.Var x))

    (defn #_"Object" Var''-get [^Var this] (.get this))
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

(defn A'new [n] (object-array n))

(defn A'clone  [^"[Ljava.lang.Object;" a]     (aclone a))
(defn A'get    [^"[Ljava.lang.Object;" a i]   (aget a i))
(defn A'length [^"[Ljava.lang.Object;" a]     (alength a))
(defn A'set    [^"[Ljava.lang.Object;" a i x] (aset a i x))

(defn new* [^Class c & s] (.newInstance ^Constructor (first (.getConstructors c)), (A'new s)))

(about #_"defp, defq, defr, defm"

(about #_"defproto"

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

(about #_"defarray"

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
                                `(valAt [this# k#] (ILookup''valAt this# k# nil))
                                `(valAt [this# k# else#] (-/if-some [x# (case (name k#) ~@s nil)] (aget (. this# ~a) x#) else#))
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
)

(about #_"defassoc"

(defn- emit-defassoc* [tname cname interfaces methods opts]
    (let [
        classname  (with-meta (symbol (str (namespace-munge *ns*) "." cname)) (meta cname))
        interfaces (vec interfaces)
    ]
        (let [a '__assoc]
            (let [eqhash
                    (fn [[i m]]
                        [
                            (conj i 'clojure.lang.IHashEq)
                            (conj m
                                `(equals [this# that#] (-/and (instance? ~tname that#) (.equals (. this# ~a) (. that# ~a))))
                            )
                        ]
                    )
                  ilookup
                    (fn [[i m]]
                        [
                            (conj i 'clojure.lang.ILookup)
                            (conj m
                                `(valAt [this# k#] (.valAt this# k# nil))
                                `(valAt [this# k# else#] (.valAt (. this# ~a) k# else#))
                            )
                        ]
                    )
                  imap
                    (fn [[i m]]
                        [
                            (conj i 'clojure.lang.IPersistentMap)
                            (conj m
                                `(count [this#] (.count (. this# ~a)))
                                `(containsKey [this# k#] (.containsKey (. this# ~a) k#))
                                `(entryAt [this# k#] (.entryAt (. this# ~a) k#))
                                `(seq [this#] (.seq (. this# ~a)))
                                `(assoc [this# k# v#] (new ~tname (.assoc (. this# ~a) k# v#)))
                                `(without [this# k#] (new ~tname (.without (. this# ~a) k#)))
                            )
                        ]
                    )]
                (let [[i m] (-/-> [interfaces methods] eqhash ilookup imap)]
                    `(eval '~(read-string (str (list* 'deftype* (symbol (name (ns-name *ns*)) (name tname)) classname (vector a) :implements (vec i) m))))
                )
            )
        )
    )
)

(defmacro defassoc [name & opts+specs]
    (let [[interfaces methods opts] (parse-opts+specs opts+specs)]
        `(do
            ~(emit-defassoc* name name (vec interfaces) methods opts)
            (eval '~(list (symbol "clojure.core/import*") (str (namespace-munge *ns*) "." name)))
        )
    )
)
)

(about #_"extend"

(defn- extend [atype & proto+mmaps]
    (doseq [[proto mmap] (partition 2 proto+mmaps)]
        (-/when-not (#'-/protocol? proto)
            (throw! (str proto " is not a protocol"))
        )
        (-/when (#'-/implements? proto atype)
            (throw! (str atype " already directly implements " (:on-interface proto) " for protocol " (:var proto)))
        )
        (alter-var-root (:var proto) assoc-in [:impls atype] mmap)
    )
)

(defn- emit-impl* [_ [p fs]]
    [p (zipmap (map (fn [%] (-/-> % first name keyword)) fs) (map (fn [%] (let [% (next %)] (if (= '=> (first %)) (second %) (cons `fn %)))) fs))]
)

(defmacro extend-type [t & specs]
    `(#'extend ~t ~@(mapcat (partial emit-impl* t) (parse-impls specs)))
)
)

(defmacro defp [p & s]                                      `(do (defproto ~p ~@s)             '~p))
(defmacro defq [r f & s] (let [c (symbol (str r "'class"))] `(do (defarray ~c ~(vec f) ~r ~@s) '~c)))
(defmacro defr [r]       (let [c (symbol (str r "'class"))] `(do (defassoc ~c ~r)              '~c)))
(defmacro defm [r & s]   (let [i `(:on-interface ~r)]       `(do (extend-type ~i ~@s)          ~i)))
)

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
            (let-when [f (first s)] (-/seq? f) => (list f x)
                `(~(first f) ~x ~@(next f))
            )
            (next s)
        )
    )
)

(about #_"cloiure.core"

(declare destructure-)

(defn- destructure-vec- [v x y]
    (let [v' (gensym "v__") s' (gensym "s__") f' (gensym "f__") amp (some (fn [%] (= % '&)) x)]
        (loop-when [v (let [v (conj v v' y)] (if amp (conj v s' `(seq ~v')) v)) n 0 s (seq x) amp? false] s => v
            (if (= (first s) '&)
                (recur (destructure- v (second s) s') n (next (next s)) true)
                (when-not amp? => (throw! "malformed binding form")
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

(defn destructure- [v x y]
    (cond
        (symbol? x) (conj v x y)
        (vector? x) (destructure-vec- v x y)
        :else       (throw! (str "unsupported binding form: " x))
    )
)

(defn destructure [bindings]
    (let [pairs (partition 2 bindings)]
        (if (every? symbol? (map first pairs))
            bindings
            (reduce (fn [%1 %2] (destructure- %1 (first %2) (second %2))) (vector) pairs)
        )
    )
)

#_(defmacro let [bindings & body]
    `(let* ~(destructure bindings) ~@body)
)

#_(defmacro loop [bindings & body]
    (if (= (destructure bindings) bindings)
        `(loop* ~bindings ~@body)
        (let [s (take-nth 2 bindings) s' (map (fn [%] (if (symbol? %) % (gensym))) s)
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
)

(ns beagle.core
    (:refer-clojure :only [])
    (:refer beagle.bore :only
        [
            Appendable''append
            Character'digit Character'isWhitespace Character'valueOf
            Integer'parseInt
            Number''toString
            Object'array Object''toString
            String''charAt String''endsWith String''indexOf String''length String''substring
            StringBuilder'new StringBuilder''append StringBuilder''toString
            System'arraycopy System'in System'out
            Array'get Array'getLength
            Flushable''flush
            PrintWriter''println
            PushbackReader''unread
            Reader''read
            Pattern'compile Pattern''matcher
            Matcher''matches
            ILookup''valAt
            Keyword''sym
            Namespace''-getMapping Namespace''-intern Namespace''-findInternedVar
            Var''-get
            AtomicReference'new AtomicReference''compareAndSet AtomicReference''get AtomicReference''set
            A'new A'clone A'get A'length A'set
        ]
    )
    (:require [beagle.bore :as -])
)

(-/import!)

(-/refer! beagle.bore [< <= -> == about and array? array-map atom bit-and bit-shift-left bit-shift-right char char? clojure-ilookup? clojure-keyword? clojure-namespace? clojure-symbol? clojure-var? cond declare defm defmethod defp defq defr extend-protocol get identical? if-not if-some instance? int int! int? let let-when loop loop-when loop-when-recur name namespace new* ns-name number? or recur-when satisfies? str string? symbol symbol? the-ns throw! unchecked-add-int unchecked-dec-int unchecked-inc-int unchecked-subtract-int vec when when-not when-some])

(-/defmacro λ [& s] (-/cons 'fn* s))

(def identical? -/identical?)

(def nil?  (λ [x] (identical? x nil)))
(def not   (λ [x] (if x false true)))
(def some? (λ [x] (not (nil? x))))

(-/about #_"beagle.Seqable"
    (-/defp Seqable
        (#_"seq" Seqable'''seq [#_"Seqable" this])
    )

    (-/extend-protocol Seqable clojure.lang.Seqable
        (Seqable'''seq [x] (.seq x))
    )

    (def seqable? (λ [x] (-/satisfies? Seqable x)))

    (def #_"seq" seq (λ [x] (-/when (some? x) (Seqable'''seq x))))

    (def empty? (λ [x] (not (seq x))))
)

(-/about #_"beagle.ISeq"
    (-/defp ISeq
        (#_"Object" ISeq'''first [#_"seq" this])
        (#_"seq" ISeq'''next [#_"seq" this])
    )

    (-/extend-protocol ISeq clojure.lang.ISeq
        (ISeq'''first [s] (.first s))
        (ISeq'''next [s] (.next s))
    )

    (def seq? (λ [x] (-/satisfies? ISeq x)))

    (def first (λ [s] (if (seq? s) (ISeq'''first s) (-/when-some [s (seq s)] (ISeq'''first s)))))

    (def #_"seq" next (λ [s] (if (seq? s) (ISeq'''next s) (-/when-some [s (seq s)] (ISeq'''next s)))))

    (def second (λ [s] (first (next s))))
    (def third  (λ [s] (first (next (next s)))))
    (def fourth (λ [s] (first (next (next (next s))))))

    (def reduce (λ [f r s] (-/if-some [s (seq s)] (recur f (f r (first s)) (next s)) r)))

    (def reduce-kv (λ [f r kvs] (-/if-some [kvs (seq kvs)] (recur f (f r (first kvs) (second kvs)) (next (next kvs))) r)))
)

(-/about #_"beagle.IObject"
    (-/defp IObject
        (#_"boolean" IObject'''equals [#_"IObject" this, #_"Object" that])
    )

    (-/extend-protocol IObject java.lang.Object
        (IObject'''equals [this, that] (.equals this, that))
    )
)

(-/about #_"beagle.IAppend"
    (-/defp IAppend
        (#_"Appendable" IAppend'''append [#_"IAppend" this, #_"Appendable" a])
    )
)

(-/about #_"beagle.Counted"
    (-/defp Counted
        (#_"int" Counted'''count [#_"Counted" this])
    )

    (-/extend-protocol Counted
        clojure.lang.Counted (Counted'''count [o] (.count o))
        java.lang.String     (Counted'''count [s] (.length s))
    )

    (-/extend-protocol Counted
        (do Object'array) (Counted'''count [a] (Array'getLength a))
    )

    (def counted? (λ [x] (-/satisfies? Counted x)))

    (-/declare + inc neg? <)

    (def count' (λ [x m]
        (-/cond
            (nil? x)
                0
            (counted? x)
                (Counted'''count x)
            (seqable? x)
                (-/loop-when [n 0 s (seq x)] (-/and (some? s) (-/or (neg? m) (< n m))) => n
                    (-/when (counted? s) => (recur (inc n) (next s))
                        (+ n (Counted'''count s))
                    )
                )
            :else
                (-/throw! (-/str "count not supported on " x))
        )
    ))

    (def count (λ [x] (count' x -1)))
)

(-/about #_"beagle.IFn"
    (-/defp IFn
        (#_"Object" IFn'''applyTo [#_"fn" this, #_"seq" args])
    )

    (-/extend-protocol IFn clojure.lang.IFn
        (IFn'''applyTo [this, args] (.applyTo this, args))
    )

    (-/declare cons)

    (def spread (λ [s]
        (-/cond
            (nil? s) nil
            (nil? (next s)) (seq (first s))
            :else (cons (first s) (spread (next s)))
        )
    ))

    (def apply (λ [#_"fn" f & s] (IFn'''applyTo f, (spread s))))
)

(-/about #_"beagle.IMeta"
    (-/defp IMeta
        (#_"meta" IMeta'''meta [#_"IMeta" this])
    )

    (-/extend-protocol IMeta clojure.lang.IMeta
        (IMeta'''meta [this] (.meta this))
    )

    (def meta (λ [x] (-/when (-/satisfies? IMeta x) (IMeta'''meta #_"IMeta" x))))
)

(-/about #_"beagle.IDeref"
    (-/defp IDeref
        (#_"Object" IDeref'''deref [#_"IDeref" this])
    )

    (-/extend-protocol IDeref clojure.lang.IDeref
        (IDeref'''deref [this] (.deref this))
    )

    (def deref (λ [#_"IDeref" ref] (IDeref'''deref ref)))
)

(-/about #_"beagle.IAtom"
    (-/defp IAtom
        (#_"Object" IAtom'''swap [#_"IAtom" this, #_"fn" f, #_"seq" args])
        (#_"Object" IAtom'''reset [#_"IAtom" this, #_"Object" o'])
    )

    (-/extend-protocol IAtom clojure.lang.IAtom2
        (IAtom'''swap  [this, f, args] (.swap  this, f, args))
        (IAtom'''reset [this,    o']   (.reset this, o'))
    )
)

(-/about #_"beagle.Sequential"
    (-/defp Sequential)

    (-/extend-protocol Sequential clojure.lang.Sequential)

    (def sequential? (λ [x] (-/satisfies? Sequential x)))
)

(-/about #_"beagle.Indexed"
    (-/defp Indexed
        (#_"Object" Indexed'''nth [#_"Indexed" this, #_"int" i])
    )

    (-/extend-protocol Indexed clojure.lang.Indexed
        (Indexed'''nth [this, i] (.nth this, i))
    )

    (def indexed? (λ [x] (-/satisfies? Indexed x)))
)

(-/about #_"beagle.ILookup"
    (-/defp ILookup
        (#_"Object" ILookup'''valAt [#_"ILookup" this, #_"key" key])
    )
)

(-/about #_"beagle.IMapEntry"
    (-/defp IMapEntry
        (#_"Object" IMapEntry'''key [#_"IMapEntry" this])
        (#_"Object" IMapEntry'''val [#_"IMapEntry" this])
    )

    (-/extend-protocol IMapEntry clojure.lang.IMapEntry
        (IMapEntry'''key [this] (.key this))
        (IMapEntry'''val [this] (.val this))
    )

    (def map-entry? (λ [x] (-/satisfies? IMapEntry x)))

    (def key (λ [#_"IMapEntry" e] (IMapEntry'''key e)))
    (def val (λ [#_"IMapEntry" e] (IMapEntry'''val e)))

    (-/declare map)

    (def not-empty (λ [coll] (-/when (seq coll) coll)))

    (def keys (λ [m] (not-empty (map key m))))
    (def vals (λ [m] (not-empty (map val m))))
)

(-/about #_"beagle.Associative"
    (-/defp Associative
        (#_"Associative" Associative'''assoc [#_"Associative" this, #_"key" key, #_"value" val])
        (#_"boolean" Associative'''containsKey [#_"Associative" this, #_"key" key])
        (#_"IMapEntry" Associative'''entryAt [#_"Associative" this, #_"key" key])
    )

    (-/extend-protocol Associative clojure.lang.Associative
        (Associative'''assoc [this, key, val] (.assoc this, key, val))
        (Associative'''containsKey [this, key] (.containsKey this, key))
        (Associative'''entryAt [this, key] (.entryAt this, key))
    )

    (def associative? (λ [x] (-/satisfies? Associative x)))

    (-/declare PersistentMap'new anew)

    (def assoc (λ [#_"Associative" a k v] (if (some? a) (Associative'''assoc a, k, v) (PersistentMap'new (anew [k, v])))))

    (-/declare get)

    (def update (λ [m k f] (assoc m k (f (get m k)))))
)

(-/about #_"beagle.IPersistentMap"
    (-/defp IPersistentMap
        (#_"IPersistentMap" IPersistentMap'''dissoc [#_"IPersistentMap" this, #_"key" key])
    )

    (-/extend-protocol IPersistentMap clojure.lang.IPersistentMap
        (IPersistentMap'''dissoc [this, key] (.without this, key))
    )

    (def map? (λ [x] (-/satisfies? IPersistentMap x)))

    (def dissoc (λ [#_"IPersistentMap" m k] (-/when (some? m) (IPersistentMap'''dissoc m, k))))
)

(-/about #_"beagle.IPersistentVector"
    (-/defp IPersistentVector)

    (-/extend-protocol IPersistentVector clojure.lang.IPersistentVector)

    (def vector? (λ [x] (-/satisfies? IPersistentVector x)))
)

(-/about #_"beagle.Atom"
    (-/defp Atom)
)

(-/about #_"beagle.Symbol"
    (-/defp Symbol)

    (-/extend-protocol Symbol clojure.lang.Symbol)

    (def symbol? (λ [x] (-/satisfies? Symbol x)))
)

(-/about #_"beagle.Keyword"
    (-/defp Keyword)

    (-/extend-protocol Keyword clojure.lang.Keyword)

    (def keyword? (λ [x] (-/satisfies? Keyword x)))
)

(-/about #_"beagle.Closure"
    (-/defp Closure)
)

(-/about #_"beagle.LazySeq"
    (-/defp LazySeq)

    (def lazy-seq? (λ [x] (-/satisfies? LazySeq x)))
)

(-/about #_"beagle.ArraySeq"
    (-/defp ArraySeq)
)

(-/about #_"beagle.Cons"
    (-/defp Cons0)
    (-/defp Cons)
)

(-/about #_"beagle.MapEntry"
    (-/defp VSeq)
    (-/defp MapEntry)
)

(-/about #_"beagle.Namespace"
    (-/defp Namespace)
)

(-/about #_"beagle.PersistentMap"
    (-/defp MSeq)
    (-/defp PersistentMap)
)

(-/about #_"beagle.Var"
    (-/defp Var)

    (-/extend-protocol Var clojure.lang.Var)

    (def var? (λ [v] (-/satisfies? Var v)))
)

(-/about #_"defarray"
    (def aget    (λ [a i] (A'get a i)))
    (def alength (λ [a]   (A'length a)))

    (def aclone (λ [a]         (-/when (some? a) (A'clone a))))
    (def acopy! (λ [a i b j n] (System'arraycopy b, j, a, i, n) a))
    (def aset!  (λ [a i x]     (A'set a i x) a))
    (def aswap! (λ [a i f & s] (aset! a i (apply f (aget a i) s))))

    (def anew (λ [size-or-seq]
        (if (-/number? size-or-seq)
            (A'new (-/int! size-or-seq))
            (-/let [#_"seq" s (seq size-or-seq) #_"int" n (count s)]
                (-/loop-when-recur [#_"array" a (A'new n) #_"int" i 0 s s] (-/and (< i n) (some? s)) [(aset! a i (first s)) (inc i) (next s)] => a)
            )
        )
    ))
)

(-/about #_"append, str, pr, prn"
    (def #_"{char String}" char-name-string
        (-/array-map
            \newline "newline"
            \space   "space"
        )
    )

    (def #_"Appendable" append-chr (λ [#_"Appendable" a, #_"char" x]
        (-/-> a (Appendable''append "\\") (Appendable''append (-/get char-name-string x x)))
    ))

    (def #_"{char String}" char-escape-string
        (-/array-map
            \newline "\\n"
            \"       "\\\""
            \\       "\\\\"
        )
    )

    (def #_"Appendable" append-str (λ [#_"Appendable" a, #_"String" x]
        (-/let [
            a (Appendable''append a, "\"")
            a (reduce (λ [%1 %2] (Appendable''append %1, (-/get char-escape-string %2 %2))) a x)
            a (Appendable''append a, "\"")
        ]
            a
        )
    ))

    (def #_"Appendable" append* (λ [#_"Appendable" a, #_"String" b, #_"fn" f'append, #_"String" c, #_"String" d, #_"Seqable" q]
        (-/let [a (-/let-when [a (Appendable''append a, b) #_"seq" s (seq q)] (some? s) => a
                    (-/loop [a a s s]
                        (-/let-when [a (f'append a (first s)) s (next s)] (some? s) => a
                            (recur (Appendable''append a, c) s)
                        )
                    )
                )]
            (Appendable''append a, d)
        )
    ))

    (-/declare append)

    (def #_"Appendable" append-seq (λ [#_"Appendable" a, #_"seq" x]    (append* a "(" append " " ")" x)))
    (def #_"Appendable" append-vec (λ [#_"Appendable" a, #_"vector" x] (append* a "[" append " " "]" x)))
    (def #_"Appendable" append-map (λ [#_"Appendable" a, #_"map" x]    (append* a "{" (λ [a e] (-/-> a (append (key e)) (Appendable''append " ") (append (val e)))) ", " "}" x)))

    (-/declare =)

    (def #_"Appendable" append (λ [#_"Appendable" a, #_"any" x]
        (-/cond
            (= x nil)              (Appendable''append a, "nil")
            (= x false)            (Appendable''append a, "false")
            (= x true)             (Appendable''append a, "true")
            (-/number? x)            (Appendable''append a, (Number''toString x))
            (-/string? x)            (append-str a x)
            (-/satisfies? IAppend x) (IAppend'''append x, a)
            (seq? x)               (append-seq a x)
            (vector? x)            (append-vec a x)
            (map? x)               (append-map a x)
            (-/char? x)              (append-chr a x)
            :else                  (Appendable''append a, (Object''toString x))
        )
    ))

    (def #_"Appendable" append! (λ [#_"Appendable" a, #_"any" x]
        (if (-/or (-/string? x) (-/char? x)) (Appendable''append a, x) (append a x))
    ))

    (def #_"String" str (λ
        ([] "")
        ([x] (if (some? x) (-/-> (StringBuilder'new) (append! x) (StringBuilder''toString)) ""))
        ([x & s]
            ((λ [#_"StringBuilder" sb s] (-/recur-when s [(append! sb (first s)) (next s)] => (StringBuilder''toString sb)))
                (-/-> (StringBuilder'new) (append! x)) s
            )
        )
    ))

    (def space   (λ [] (Appendable''append System'out \space)   nil))
    (def newline (λ [] (Appendable''append System'out \newline) nil))
    (def flush   (λ [] (Flushable''flush   System'out)          nil))

    (def pr (λ
        ([] nil)
        ([x] (append System'out x) nil)
        ([x & s]
            (pr x) (space)
            (-/let-when [[x & s] s] (some? s) => (pr x)
                (recur x s)
            )
        )
    ))

    (def print (λ
        ([] nil)
        ([x] (append! System'out x) nil)
        ([x & s]
            (print x) (space)
            (-/let-when [[x & s] s] (some? s) => (print x)
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
        (-/new* Atom'class (anew [(AtomicReference'new data)]))
    ))

    (def #_"Object" Atom''deref (λ [#_"Atom" this]
        (AtomicReference''get (get this :data))
    ))

    (def #_"Object" Atom''swap (λ [#_"Atom" this, #_"fn" f, #_"seq" args]
        (-/loop []
            (-/let [#_"Object" o (AtomicReference''get (get this :data)) #_"Object" o' (apply f o args)]
                (-/when (AtomicReference''compareAndSet (get this :data), o, o') => (recur)
                    o'
                )
            )
        )
    ))

    (def #_"Object" Atom''reset (λ [#_"Atom" this, #_"Object" o']
        (AtomicReference''set (get this :data), o')
        o'
    ))

    (-/defm Atom IDeref
        (IDeref'''deref => Atom''deref)
    )

    (-/defm Atom IAtom
        (IAtom'''swap => Atom''swap)
        (IAtom'''reset => Atom''reset)
    )
)

(def atom (λ [x] (Atom'new x)))

(def swap! (λ [#_"IAtom" a f & args] (IAtom'''swap a, f, args)))

(def reset! (λ [#_"IAtom" a x'] (IAtom'''reset a, x')))
)

(-/about #_"beagle.Util"

(-/about #_"Util"
    (-/declare Symbol''equals Keyword''equals)

    (def #_"boolean" Util'equiv (λ [#_"Object" a, #_"Object" b]
        (-/cond
            (identical? a b)              true
            (nil? a)                      false
            (-/and (-/number? a) (-/number? b)) (-/== a b)
            (-/or (seq? a) (map? a) (vector? a)) (IObject'''equals a, b)
            (-/or (seq? b) (map? b) (vector? b)) (IObject'''equals b, a)
            (-/instance? (get Symbol :on-interface) a)  (Symbol''equals a, b)
            (-/instance? (get Symbol :on-interface) b)  (Symbol''equals b, a)
            (-/instance? (get Keyword :on-interface) a) (Keyword''equals a, b)
            (-/instance? (get Keyword :on-interface) b) (Keyword''equals b, a)
            :else                         (IObject'''equals a, b)
        )
    ))
)

(def = (λ [x y] (Util'equiv x y)))

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
    (-/declare Symbol''equals)

    (-/defq Symbol [#_"String" ns, #_"String" name]
        clojure.lang.Named (getNamespace [_] (get _ :ns)) (getName [_] (get _ :name))
        java.lang.Object (equals [_, o] (Symbol''equals _, o)) (toString [_] (str _))
    )

    (def #_"Symbol" Symbol'new (λ [#_"String" ns, #_"String" name]
        (-/new* Symbol'class (anew [ns, name]))
    ))

    (def #_"Symbol" Symbol'intern (λ [#_"String" nsname]
        (-/let [#_"int" i (String''indexOf nsname, (-/int \/))]
            (if (-/or (= i -1) (= nsname "/"))
                (Symbol'new nil, nsname)
                (Symbol'new (String''substring nsname, 0, i), (String''substring nsname, (inc i)))
            )
        )
    ))

    (def #_"boolean" Symbol''equals (λ [#_"Symbol" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (-/symbol? that) (= (get this :ns) (-/namespace that)) (= (get this :name) (-/name that)))
            (-/and (symbol? that) (= (get this :ns) (get that :ns)) (= (get this :name) (get that :name)))
        )
    ))

    (def #_"Appendable" Symbol''append (λ [#_"Symbol" this, #_"Appendable" a]
        (if (some? (get this :ns)) (-/-> a (Appendable''append (get this :ns)) (Appendable''append "/") (Appendable''append (get this :name))) (Appendable''append a, (get this :name)))
    ))

    (-/defm Symbol IObject
        (IObject'''equals => Symbol''equals)
    )

    (-/defm Symbol IAppend
        (IAppend'''append => Symbol''append)
    )
)

(def symbol (λ [name] (if (symbol? name) name (Symbol'intern name))))

(def symbol! (λ [s] (symbol (if (-/clojure-symbol? s) (str s) s))))

(-/defmethod -/print-method (get Symbol :on-interface) [o w] (.write w, (str o)))
)

(-/about #_"beagle.Keyword"

(-/about #_"Keyword"
    (-/declare Keyword''equals)

    (-/defq Keyword [#_"Symbol" sym]
        clojure.lang.Named (getNamespace [_] (get (get _ :sym) :ns)) (getName [_] (get (get _ :sym) :name))
        java.lang.Object (equals [_, o] (Keyword''equals _, o)) (toString [_] (str _))
    )

    (def #_"Keyword" Keyword'new (λ [#_"Symbol" sym]
        (-/new* Keyword'class (anew [sym]))
    ))

    (def #_"boolean" Keyword''equals (λ [#_"Keyword" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (-/clojure-keyword? that) (Symbol''equals (get this :sym), (Keyword''sym that)))
            (-/and (keyword? that) (Symbol''equals (get this :sym), (get that :sym)))
        )
    ))

    (def #_"Appendable" Keyword''append (λ [#_"Keyword" this, #_"Appendable" a]
        (-/-> a (Appendable''append ":") (append (get this :sym)))
    ))

    (-/defm Keyword IObject
        (IObject'''equals => Keyword''equals)
    )

    (-/defm Keyword IAppend
        (IAppend'''append => Keyword''append)
    )
)

(def keyword (λ [name]
    (-/cond
        (keyword? name) name
        (symbol? name) (Keyword'new #_"Symbol" name)
        (-/string? name) (Keyword'new (symbol #_"String" name))
    )
))

(def keyword! (λ [k] (keyword (if (-/clojure-keyword? k) (-/name k) k))))

(-/defmethod -/print-method (get Keyword :on-interface) [o w] (.write w, (str o)))
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

    (def #_"Object" Closure''applyTo (λ [#_"Closure" this, #_"seq" args]
        (-/let [
            #_"FnMethod" fm
                (-/let [#_"int" m (inc Compiler'MAX_POSITIONAL_ARITY) #_"int" n (min (count' args m) m)]
                    (-/or (get (get (get this :fun) :regulars) n)
                        (-/let-when [fm (get (get this :fun) :variadic)] (-/and (some? fm) (<= (dec (- 0 (get fm :arity))) n)) => (Closure'throwArity this, (if (< n m) n (- 0 m)))
                            fm
                        )
                    )
                )
            #_"array" vars
                (-/let [
                    #_"int" m (inc (reduce max (inc -1) (map (λ [%] (get % :idx)) (vals (deref (get fm :'locals))))))
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

    (-/defm Closure IFn
        (IFn'''applyTo => Closure''applyTo)
    )
)
)

(-/about #_"beagle.Cons"

(-/about #_"Cons0"
    (-/declare Cons0''seq Cons0''first Cons0''next Cons0''equals)

    (-/defq Cons0 []
        clojure.lang.ISeq (seq [_] (Cons0''seq _)) (first [_] (Cons0''first _)) (next [_] (Cons0''next _)) (more [_] (-/or (Cons0''next _) ()))
    )

    (def #_"Cons0" Cons0'new (λ []
        (-/new* Cons0'class (anew []))
    ))

    (def #_"boolean" Cons0''equals (λ [#_"Cons0" this, #_"Object" that]
        (-/and (sequential? that) (nil? (seq that)))
    ))

    (def #_"seq" Cons0''seq (λ [#_"Cons0" this]
        nil
    ))

    (def #_"Object" Cons0''first (λ [#_"Cons0" this]
        nil
    ))

    (def #_"seq" Cons0''next (λ [#_"Cons0" this]
        nil
    ))

    (def #_"int" Cons0''count (λ [#_"Cons0" this]
        0
    ))

    (-/defm Cons0 Sequential)

    (-/defm Cons0 IObject
        (IObject'''equals => Cons0''equals)
    )

    (-/defm Cons0 Seqable
        (Seqable'''seq => Cons0''seq)
    )

    (-/defm Cons0 ISeq
        (ISeq'''first => Cons0''first)
        (ISeq'''next => Cons0''next)
    )

    (-/defm Cons0 Counted
        (Counted'''count => Cons0''count)
    )

    (def #_"Cons0" Cons'nil (Cons0'new))
)

(-/about #_"Cons"
    (-/declare Cons''seq Cons''next Cons''count)

    (-/defq Cons [#_"Object" car, #_"seq" cdr]
        clojure.lang.ISeq (seq [_] (Cons''seq _)) (first [_] (get _ :car)) (next [_] (Cons''next _)) (more [_] (-/or (Cons''next _) ()))
        clojure.lang.IPersistentCollection (count [_] (Cons''count _))
        clojure.lang.Sequential
    )

    (def #_"Cons" Cons'new (λ [#_"Object" car, #_"seq" cdr]
        (-/new* Cons'class (anew [car, cdr]))
    ))

    (def #_"seq" Cons''seq (λ [#_"Cons" this]
        this
    ))

    (def #_"seq" Cons''next (λ [#_"Cons" this]
        (seq (get this :cdr))
    ))

    (def #_"int" Cons''count (λ [#_"Cons" this]
        (inc (count (get this :cdr)))
    ))

    (def #_"boolean" Cons''equals (λ [#_"Cons" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (sequential? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))

    (-/defm Cons Sequential)

    (-/defm Cons Seqable
        (Seqable'''seq => Cons''seq)
    )

    (-/defm Cons ISeq
        (ISeq'''first => (λ [%] (get % :car)))
        (ISeq'''next => Cons''next)
    )

    (-/defm Cons Counted
        (Counted'''count => Cons''count)
    )

    (-/defm Cons IObject
        (IObject'''equals => Cons''equals)
    )
)

(def cons (λ [x s] (Cons'new x, (seq s))))

(def reverse (λ [s] (reduce (λ [%1 %2] (cons %2 %1)) Cons'nil s)))

(def list (λ [& s] (if (some? s) (reverse (reverse s)) Cons'nil)))
)

(-/about #_"beagle.ArraySeq"

(-/about #_"ArraySeq"
    (-/declare ArraySeq''seq ArraySeq''first ArraySeq''next)

    (-/defq ArraySeq [#_"array" a, #_"int" i]
        clojure.lang.ISeq (seq [_] (ArraySeq''seq _)) (first [_] (ArraySeq''first _)) (next [_] (ArraySeq''next _)) (more [_] (-/or (ArraySeq''next _) ()))
        clojure.lang.Sequential
    )

    (def #_"ArraySeq" ArraySeq'new (λ [#_"array" a, #_"int" i]
        (-/new* ArraySeq'class (anew [a, i]))
    ))

    (def #_"ArraySeq" ArraySeq'create (λ [#_"array" a]
        (-/when (-/and (some? a) (pos? (alength a)))
            (ArraySeq'new a, 0)
        )
    ))

    (-/extend-protocol Seqable (do Object'array)
        (#_"ArraySeq" Seqable'''seq [#_"array" a] (ArraySeq'create a))
    )

    (def #_"seq" ArraySeq''seq (λ [#_"ArraySeq" this]
        this
    ))

    (def #_"Object" ArraySeq''first (λ [#_"ArraySeq" this]
        (-/when (some? (get this :a))
            (aget (get this :a) (get this :i))
        )
    ))

    (def #_"seq" ArraySeq''next (λ [#_"ArraySeq" this]
        (-/when (-/and (some? (get this :a)) (< (inc (get this :i)) (count (get this :a))))
            (ArraySeq'new (get this :a), (inc (get this :i)))
        )
    ))

    (def #_"int" ArraySeq''count (λ [#_"ArraySeq" this]
        (if (some? (get this :a)) (- (count (get this :a)) (get this :i)) 0)
    ))

    (def #_"boolean" ArraySeq''equals (λ [#_"ArraySeq" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (sequential? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))

    (-/defm ArraySeq Sequential)

    (-/defm ArraySeq Seqable
        (Seqable'''seq => ArraySeq''seq)
    )

    (-/defm ArraySeq ISeq
        (ISeq'''first => ArraySeq''first)
        (ISeq'''next => ArraySeq''next)
    )

    (-/defm ArraySeq Counted
        (Counted'''count => ArraySeq''count)
    )

    (-/defm ArraySeq IObject
        (IObject'''equals => ArraySeq''equals)
    )
)
)

(-/about #_"beagle.LazySeq"

(-/about #_"LazySeq"
    (-/declare LazySeq''seq LazySeq''first LazySeq''next)

    (-/defq LazySeq [#_"fn'" f, #_"Object'" o, #_"seq'" s]
        clojure.lang.ISeq (seq [_] (LazySeq''seq _)) (first [_] (LazySeq''first _)) (next [_] (LazySeq''next _)) (more [_] (-/or (LazySeq''next _) ()))
        clojure.lang.Sequential
    )

    (def #_"LazySeq" LazySeq'new (λ [#_"fn" f]
        (-/new* LazySeq'class (anew [(atom f), (atom nil), (atom nil)]))
    ))

    (def #_"seq" LazySeq''seq (λ [#_"LazySeq" this]
        (do #_"locking this"
            (-/let [step-
                    (λ [this]
                        (-/when-some [#_"fn" f (deref (get this :f))]
                            (reset! (get this :f) nil)
                            (reset! (get this :o) (f))
                        )
                        (-/or (deref (get this :o)) (deref (get this :s)))
                    )]
                (step- this)
                (-/when-some [#_"Object" o (deref (get this :o))]
                    (reset! (get this :o) nil)
                    (reset! (get this :s) (-/loop-when-recur o (lazy-seq? o) (step- o) => (seq o)))
                )
                (deref (get this :s))
            )
        )
    ))

    (def #_"Object" LazySeq''first (λ [#_"LazySeq" this]
        (-/when-some [#_"seq" s (seq this)]
            (first s)
        )
    ))

    (def #_"seq" LazySeq''next (λ [#_"LazySeq" this]
        (-/when-some [#_"seq" s (seq this)]
            (next s)
        )
    ))

    (def #_"boolean" LazySeq''equals (λ [#_"LazySeq" this, #_"Object" that]
        (-/if-some [#_"seq" s (seq this)]
            (= s that)
            (-/and (sequential? that) (nil? (seq that)))
        )
    ))

    (-/defm LazySeq Sequential)

    (-/defm LazySeq Seqable
        (Seqable'''seq => LazySeq''seq)
    )

    (-/defm LazySeq ISeq
        (ISeq'''first => LazySeq''first)
        (ISeq'''next => LazySeq''next)
    )

    (-/defm LazySeq IObject
        (IObject'''equals => LazySeq''equals)
    )
)

(def lazy-seq (λ [f] (LazySeq'new f)))

(def dorun (λ [s]
    (-/when-some [s (seq s)]
        (recur (next s))
    )
))

(def doall (λ [s] (dorun s) s))

(def comp (λ [f g] (λ [x] (f (g x)))))

(def map (λ [f s]
    (lazy-seq
        (λ []
            (-/when-some [s (seq s)]
                (cons (f (first s)) (map f (next s)))
            )
        )
    )
))
)

(-/about #_"beagle.MapEntry"

(-/about #_"VSeq"
    (-/declare VSeq''seq VSeq''first VSeq''next)

    (-/defq VSeq [#_"pair" v, #_"int" i]
        clojure.lang.ISeq (seq [_] (VSeq''seq _)) (first [_] (VSeq''first _)) (next [_] (VSeq''next _)) (more [_] (-/or (VSeq''next _) ()))
        clojure.lang.Sequential
    )

    (def #_"VSeq" VSeq'new (λ [#_"pair" v, #_"int" i]
        (-/new* VSeq'class (anew [v, i]))
    ))

    (def #_"seq" VSeq''seq (λ [#_"VSeq" this]
        this
    ))

    (def #_"Object" VSeq''first (λ [#_"VSeq" this]
        (-/nth (get this :v) (get this :i))
    ))

    (def #_"seq" VSeq''next (λ [#_"VSeq" this]
        (-/when (< (inc (get this :i)) (count (get this :v)))
            (VSeq'new (get this :v), (inc (get this :i)))
        )
    ))

    (def #_"int" VSeq''count (λ [#_"VSeq" this]
        (- (count (get this :v)) (get this :i))
    ))

    (def #_"boolean" VSeq''equals (λ [#_"VSeq" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (sequential? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))

    (-/defm VSeq Sequential)

    (-/defm VSeq Seqable
        (Seqable'''seq => VSeq''seq)
    )

    (-/defm VSeq ISeq
        (ISeq'''first => VSeq''first)
        (ISeq'''next => VSeq''next)
    )

    (-/defm VSeq Counted
        (Counted'''count => VSeq''count)
    )

    (-/defm VSeq IObject
        (IObject'''equals => VSeq''equals)
    )
)

(-/about #_"MapEntry"
    (-/defq MapEntry [#_"key" k, #_"value" v]
        java.util.Map$Entry (getKey [_] (get _ :k)) (getValue [_] (get _ :v))
    )

    (def #_"MapEntry" MapEntry'new (λ [#_"key" k, #_"value" v]
        (-/new* MapEntry'class (anew [k, v]))
    ))

    (def #_"Object" MapEntry''nth (λ [#_"MapEntry" this, #_"int" i]
        (-/cond (= i 0) (IMapEntry'''key this) (= i 1) (IMapEntry'''val this) :else (-/throw! "index is out of bounds"))
    ))

    (def #_"int" MapEntry''count (λ [#_"MapEntry" this]
        2
    ))

    (def #_"seq" MapEntry''seq (λ [#_"MapEntry" this]
        (VSeq'new this, 0)
    ))

    (def #_"boolean" MapEntry''equals (λ [#_"MapEntry" this, #_"Object" that]
        (-/or (identical? this that)
            (-/cond
                (vector? that)
                    (-/and (= (count that) 2) (= (-/nth that 0) (IMapEntry'''key this)) (= (-/nth that 1) (IMapEntry'''val this)))
                (sequential? that)
                    (-/loop-when [#_"int" i 0 #_"seq" s (seq that)] (< i 2) => (nil? s)
                        (-/recur-when (-/and (some? s) (= (Indexed'''nth this, i) (first s))) [(inc i) (next s)] => false)
                    )
                :else
                    false
            )
        )
    ))

    (-/defm MapEntry IMapEntry
        (IMapEntry'''key => (λ [%] (get % :k)))
        (IMapEntry'''val => (λ [%] (get % :v)))
    )

    (-/defm MapEntry Sequential)

    (-/defm MapEntry Indexed
        (Indexed'''nth => MapEntry''nth)
    )

    (-/defm MapEntry Counted
        (Counted'''count => MapEntry''count)
    )

    (-/defm MapEntry Seqable
        (Seqable'''seq => MapEntry''seq)
    )

    (-/defm MapEntry IObject
        (IObject'''equals => MapEntry''equals)
    )
)
)

(-/about #_"beagle.PersistentMap"

(-/about #_"MSeq"
    (-/declare MSeq''seq MSeq''first MSeq''next)

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
        (MapEntry'new (aget (get this :a) (get this :i)), (aget (get this :a) (inc (get this :i))))
    ))

    (def #_"seq" MSeq''next (λ [#_"MSeq" this]
        (-/when (< (+ (get this :i) 2) (alength (get this :a)))
            (MSeq'new (get this :a), (+ (get this :i) 2))
        )
    ))

    (def #_"int" MSeq''count (λ [#_"MSeq" this]
        (>> (- (alength (get this :a)) (get this :i)) 1)
    ))

    (def #_"boolean" MSeq''equals (λ [#_"MSeq" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (sequential? that)
                (-/loop-when [#_"seq" s (seq this) #_"seq" z (seq that)] (some? s) => (nil? z)
                    (-/and (some? z) (= (first s) (first z)) (recur (next s) (next z)))
                )
            )
        )
    ))

    (-/defm MSeq Sequential)

    (-/defm MSeq Seqable
        (Seqable'''seq => MSeq''seq)
    )

    (-/defm MSeq ISeq
        (ISeq'''first => MSeq''first)
        (ISeq'''next => MSeq''next)
    )

    (-/defm MSeq Counted
        (Counted'''count => MSeq''count)
    )

    (-/defm MSeq IObject
        (IObject'''equals => MSeq''equals)
    )
)

(-/about #_"PersistentMap"
    (-/declare PersistentMap''seq PersistentMap''assoc PersistentMap''containsKey)

    (-/defq PersistentMap [#_"array" array]
        clojure.lang.Seqable (seq [_] (PersistentMap''seq _))
        clojure.lang.Associative (assoc [_, key, val] (PersistentMap''assoc _, key, val)) (containsKey [_, key] (PersistentMap''containsKey _, key))
    )

    (def #_"PersistentMap" PersistentMap'new (λ [#_"array" a]
        (-/new* PersistentMap'class (anew [(-/or a (anew 0))]))
    ))

    (def #_"PersistentMap" PersistentMap'EMPTY (PersistentMap'new nil))

    (def #_"PersistentMap" PersistentMap''create (λ [#_"PersistentMap" this, #_"array" init]
        (PersistentMap'new init)
    ))

    (def #_"int" PersistentMap''count (λ [#_"PersistentMap" this]
        (>> (alength (get this :array)) 1)
    ))

    (def #_"int" PersistentMap'index-of (λ [#_"array" a, #_"key" key]
        (-/loop-when [#_"int" i 0] (< i (alength a)) => -1
            (if (= (aget a i) key) i (recur (+ i 2)))
        )
    ))

    (def #_"value" PersistentMap''valAt (λ [#_"PersistentMap" this, #_"key" key]
        (-/let [
            #_"array" a (get this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (-/when (< -1 i)
                (aget a (inc i))
            )
        )
    ))

    (def #_"IPersistentMap" PersistentMap''assoc (λ [#_"PersistentMap" this, #_"key" key, #_"value" val]
        (-/let [
            #_"array" a (get this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (if (< -1 i)
                (if (= (aget a (inc i)) val)
                    this
                    (PersistentMap''create this, (-/-> (aclone a) (aset! (inc i) val)))
                )
                (-/let [
                    #_"int" n (alength a)
                    #_"array" a' (anew (+ n 2))
                    a' (if (pos? n) (acopy! a' 0 a 0 n) a')
                ]
                    (PersistentMap''create this, (-/-> a' (aset! n key) (aset! (inc n) val)))
                )
            )
        )
    ))

    (def #_"boolean" PersistentMap''containsKey (λ [#_"PersistentMap" this, #_"key" key]
        (< -1 (PersistentMap'index-of (get this :array), key))
    ))

    (def #_"pair" PersistentMap''entryAt (λ [#_"PersistentMap" this, #_"key" key]
        (-/let [
            #_"array" a (get this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (-/when (< -1 i)
                (MapEntry'new (aget a i), (aget a (inc i)))
            )
        )
    ))

    (def #_"IPersistentMap" PersistentMap''dissoc (λ [#_"PersistentMap" this, #_"key" key]
        (-/let [
            #_"array" a (get this :array) #_"int" i (PersistentMap'index-of a, key)
        ]
            (-/when (< -1 i) => this
                (-/let-when [#_"int" n (- (alength a) 2)] (pos? n) => PersistentMap'EMPTY
                    (-/let [
                        #_"array" a' (-/-> (anew n) (acopy! 0 a 0 i) (acopy! i a (+ i 2) (- n i)))
                    ]
                        (PersistentMap''create this, a')
                    )
                )
            )
        )
    ))

    (def #_"seq" PersistentMap''seq (λ [#_"PersistentMap" this]
        (-/when (pos? (alength (get this :array)))
            (MSeq'new (get this :array), 0)
        )
    ))

    (-/declare contains?)

    (def #_"boolean" PersistentMap''equals (λ [#_"PersistentMap" this, #_"Object" that]
        (-/or (identical? this that)
            (-/and (map? that) (= (count that) (count this))
                (-/loop-when [#_"seq" s (seq this)] (some? s) => true
                    (-/let [#_"pair" e (first s) #_"Object" k (key e)]
                        (-/and (contains? that k) (= (val e) (get that k))
                            (recur (next s))
                        )
                    )
                )
            )
        )
    ))

    (-/defm PersistentMap Counted
        (Counted'''count => PersistentMap''count)
    )

    (-/defm PersistentMap ILookup
        (ILookup'''valAt => PersistentMap''valAt)
    )

    (-/defm PersistentMap Associative
        (Associative'''assoc => PersistentMap''assoc)
        (Associative'''containsKey => PersistentMap''containsKey)
        (Associative'''entryAt => PersistentMap''entryAt)
    )

    (-/defm PersistentMap IPersistentMap
        (IPersistentMap'''dissoc => PersistentMap''dissoc)
    )

    (-/defm PersistentMap Seqable
        (Seqable'''seq => PersistentMap''seq)
    )

    (-/defm PersistentMap IObject
        (IObject'''equals => PersistentMap''equals)
    )
)

(def array-map (λ [& kvs] (if (some? kvs) (reduce-kv assoc PersistentMap'EMPTY kvs) PersistentMap'EMPTY)))
)

(-/about #_"beagle.RT"

(-/about #_"RT"
    (def #_"Object" RT'nth (λ [#_"Object" coll, #_"int" n]
        (-/cond
            (indexed? coll)
                (Indexed'''nth coll, n)
            (nil? coll)
                nil
            (-/string? coll)
                (Character'valueOf (String''charAt coll, n))
            (-/array? coll)
                (Array'get coll, n)
            (map-entry? coll)
                (-/let [#_"pair" e coll]
                    (-/cond (= n 0) (key e) (= n 1) (val e) :else (-/throw! "index is out of bounds"))
                )
            (sequential? coll)
                (-/loop-when [#_"int" i 0 #_"seq" s (seq coll)] (-/and (<= i n) (some? s)) => (-/throw! "index is out of bounds")
                    (-/recur-when (< i n) [(inc i) (next s)] => (first s))
                )
            :else
                (-/throw! (str "nth not supported on " coll))
        )
    ))

(def nth (λ [s i] (RT'nth s i)))

    (def #_"Object" RT'get (λ [#_"Object" coll, #_"key" key]
        (-/cond
            (-/satisfies? ILookup coll)
                (ILookup'''valAt coll, key)
            (nil? coll)
                nil
            (-/and (-/number? key) (-/or (-/string? coll) (-/array? coll)))
                (-/let-when [#_"int" n (-/int! key)] (< -1 n (count coll))
                    (nth coll n)
                )
            (-/clojure-ilookup? coll)
                (ILookup''valAt coll, key)
        )
    ))

(def get (λ [coll key] (RT'get coll key)))

    (def #_"Object" RT'contains (λ [#_"Object" coll, #_"key" key]
        (-/cond
            (nil? coll)
                false
            (associative? coll)
                (if (Associative'''containsKey coll, key) true false)
            (-/and (-/number? key) (-/or (-/string? coll) (-/array? coll)))
                (-/let [#_"int" n (-/int! key)]
                    (if (< -1 n (count coll)) true false)
                )
            :else
                (-/throw! (str "contains? not supported on " coll))
        )
    ))

(def contains? (λ [coll key] (RT'contains coll key)))

    (def #_"Object" RT'find (λ [#_"Object" coll, #_"key" key]
        (-/cond
            (nil? coll)
                nil
            (associative? coll)
                (Associative'''entryAt coll, key)
            :else
                (-/throw! (str "find not supported on " coll))
        )
    ))

(def find (λ [m k] (RT'find m k)))

    (def #_"IPersistentMap" RT'mapUniqueKeys (λ [#_"Seqable" init]
        (if (empty? init) PersistentMap'EMPTY (PersistentMap'new (anew init)))
    ))
)
)

(-/about #_"beagle.Var"

(-/about #_"Var"
    (def #_"Appendable" Var'append (λ [#_"Appendable" a, #_"Namespace" ns, #_"Symbol" sym]
        (if (some? ns)
            (-/-> a (Appendable''append "#'") (append (get ns :name)) (Appendable''append "/") (append sym))
            (-/-> a (Appendable''append "#_var nil #_\"") (append sym) (Appendable''append "\""))
        )
    ))
)

(-/about #_"Var"
    (-/declare Var''get)

    (-/defq Var [#_"Namespace" ns, #_"Symbol" sym, #_"Object'" root]
        java.util.concurrent.Future (get [_] (Var''get _))
    )

    (def #_"Var" Var'new (λ [#_"Namespace" ns, #_"Symbol" sym]
        (-/new* Var'class (anew [ns, sym, (atom nil)]))
    ))

    (def #_"meta" Var''meta (λ [#_"Var" this]
        nil
    ))

    (def #_"Appendable" Var''append (λ [#_"Var" this, #_"Appendable" a]
        (Var'append a, (get this :ns), (get this :sym))
    ))

    (def #_"Object" Var''get (λ [#_"Var" this]
        (-/when-not (-/clojure-var? this) => (Var''-get this)
            (deref (get this :root))
        )
    ))

(def var-get (λ [#_"var" x] (Var''get x)))

    (def #_"void" Var''bindRoot (λ [#_"Var" this, #_"Object" root]
        (reset! (get this :root) root)
        nil
    ))

    (-/declare Namespace''intern)

    (def #_"Var" Var'intern (λ [#_"Namespace" ns, #_"Symbol" sym, #_"Object" root]
        (-/let [#_"Var" v (Namespace''intern ns, sym)]
            (Var''bindRoot v, root)
            v
        )
    ))

(def intern (λ [ns name root] (Var'intern (-/the-ns ns), name, root)))

    (def #_"Object" Var''applyTo (λ [#_"Var" this, #_"seq" args]
        (IFn'''applyTo (deref this), args)
    ))

    (-/defm Var IMeta
        (IMeta'''meta => Var''meta)
    )

    (-/defm Var IObject
        (IObject'''equals => identical?)
    )

    (-/defm Var IAppend
        (IAppend'''append => Var''append)
    )

    (-/defm Var IDeref
        (IDeref'''deref => Var''get)
    )

    (-/defm Var IFn
        (IFn'''applyTo => Var''applyTo)
    )
)
)

(-/about #_"beagle.Namespace"

(-/about #_"Namespace"
    (-/defq Namespace [#_"Symbol" name, #_"{Symbol Var}'" mappings, #_"{Symbol Namespace}'" aliases])

    (def #_"{Symbol Namespace}'" Namespace'namespaces (atom (-/array-map)))

    (def #_"Namespace" Namespace'find (λ [#_"Symbol" name]
        (get (deref Namespace'namespaces) name)
    ))

    (def #_"Namespace" Namespace'new (λ [#_"Symbol" name]
        (-/new* Namespace'class (anew [name, (atom (-/array-map)), (atom (-/array-map))]))
    ))

    (def #_"Namespace" Namespace'findOrCreate (λ [#_"Symbol" name]
        (-/or (Namespace'find name)
            (-/let [#_"Namespace" ns (Namespace'new name)]
                (swap! Namespace'namespaces assoc name ns)
                ns
            )
        )
    ))

(def create-ns (λ [sym] (Namespace'findOrCreate sym)))

    (def #_"Appendable" Namespace''append (λ [#_"Namespace" this, #_"Appendable" a]
        (Appendable''append a, (get (get this :name) :name))
    ))

    (def #_"Object" Namespace''getMapping (λ [#_"Namespace" this, #_"Symbol" name]
        (-/when-not (-/clojure-namespace? this) => (Namespace''-getMapping this, name)
            (get (deref (get this :mappings)) name)
        )
    ))

    (def #_"var" Namespace''intern (λ [#_"Namespace" this, #_"Symbol" sym]
        (-/when-not (-/clojure-namespace? this) => (Namespace''-intern this, sym)
            (-/when (nil? (get sym :ns)) => (-/throw! "can't intern namespace-qualified symbol")
                (-/let [#_"Object" o
                        (-/or (get (deref (get this :mappings)) sym)
                            (-/let [#_"var" v (Var'new this, sym)]
                                (swap! (get this :mappings) assoc sym v)
                                v
                            )
                        )]
                    (-/when-not (-/and (var? o) (= (get o :ns) this)) => o
                        (-/let [#_"var" v (Var'new this, sym)]
                            (swap! (get this :mappings) assoc sym v)
                            v
                        )
                    )
                )
            )
        )
    ))

    (def #_"var" Namespace''findInternedVar (λ [#_"Namespace" this, #_"Symbol" name]
        (-/when-not (-/clojure-namespace? this) => (Namespace''-findInternedVar this, (-/symbol (str name)))
            (-/let [#_"Object" o (get (deref (get this :mappings)) name)]
                (-/when (-/and (var? o) (= (get o :ns) this))
                    o
                )
            )
        )
    ))

    (def #_"Namespace" Namespace''getAlias (λ [#_"Namespace" this, #_"Symbol" alias]
        (get (deref (get this :aliases)) alias)
    ))

    (def #_"void" Namespace''addAlias (λ [#_"Namespace" this, #_"Symbol" alias, #_"Namespace" ns]
        (-/when (-/and (some? alias) (some? ns)) => (-/throw! "expecting Symbol + Namespace")
            (-/let [#_"Object" o
                    (-/or (get (deref (get this :aliases)) alias)
                        (do
                            (swap! (get this :aliases) assoc alias ns)
                            ns
                        )
                    )]
                (-/when-not (= o ns)
                    (-/throw! (str "alias " alias " already exists in namespace " (get this :name) ", aliasing " o))
                )
            )
        )
        nil
    ))

(-/declare Beagle'repl)

(def alias (λ [sym ns]
    (Namespace''addAlias Beagle'repl sym (-/the-ns ns))
))

    (-/defm Namespace IObject
        (IObject'''equals => identical?)
    )

    (-/defm Namespace IAppend
        (IAppend'''append => Namespace''append)
    )
)
)

(-/about #_"beagle.Compiler"
    (-/defp Expr
        (#_"gen" Expr'''emit [#_"Expr" this, #_"Context" context, #_"map" scope, #_"gen" gen])
    )

    (-/defp Recur)

    (-/defp LiteralExpr)
    (-/defp UnresolvedVarExpr)
    (-/defp VarExpr)
    (-/defp BodyExpr)
    (-/defp IfExpr)
    (-/defp InvokeExpr)
    (-/defp LocalBinding)
    (-/defp LocalBindingExpr)
    (-/defp FnMethod)
    (-/defp FnExpr)
    (-/defp DefExpr)
    (-/defp LetExpr)
    (-/defp RecurExpr)
)

(-/about #_"beagle.Machine"

(-/about #_"Machine"
    (def #_"Object" Machine'compute (λ [#_"code" code, #_"array" vars]
        (-/loop [#_"stack" s nil #_"int" i 0]
            (-/let [[x y] (nth code i)]
                (-/cond
                    (= x :anew)     (-/let [[    a & s] s]                             (recur (cons (anew a) s)                  (inc i)))
                    (= x :apply)    (-/let [[  b a & s] s]                             (recur (cons (apply a b) s)               (inc i)))
                    (= x :aset)     (-/let [[c b a & s] s] (aset! a b c)               (recur s                                  (inc i)))
                    (= x :create)   (-/let [[    a & s] s]                             (recur (cons (Closure'new y, a) s)        (inc i)))
                    (= x :dup)      (-/let [[    a]     s]                             (recur (cons a s)                         (inc i)))
                    (= x :get)      (-/let [[    a & s] s]                             (recur (cons (get (deref (get a :_env)) y) s) (inc i)))
                    (= x :goto)                                                      (recur s                        (deref y))
                    (= x :if-eq?)   (-/let [[  b a & s] s]                             (recur s        (if     (= a b) (deref y) (inc i))))
                    (= x :if-nil?)  (-/let [[    a & s] s]                             (recur s        (if  (nil? a)   (deref y) (inc i))))
                    (= x :invoke-1) (-/let [[    a & s] s]                             (recur (cons (y a) s)                     (inc i)))
                    (= x :invoke-2) (-/let [[  b a & s] s]                             (recur (cons (y a b) s)                   (inc i)))
                    (= x :load)                                                      (recur (cons (aget vars y) s)             (inc i))
                    (= x :pop)                                                       (recur (next s)                           (inc i))
                    (= x :push)                                                      (recur (cons y s)                         (inc i))
                    (= x :return)                        (first s)
                    (= x :store)    (-/let [[    a & s] s] (aset! vars y a)            (recur s                                  (inc i)))
                    :else           nil
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

    (def Gen''mark (λ
        (#_"label" [#_"gen" gen] (atom (count gen)))
        (#_"gen" [#_"gen" gen, #_"label" label] (reset! label (count gen)) gen)
    ))

    (def #_"gen" Gen''anew    (λ [#_"gen" gen]                          (cons [:anew] gen)))
    (def #_"gen" Gen''apply   (λ [#_"gen" gen]                          (cons [:apply] gen)))
    (def #_"gen" Gen''aset    (λ [#_"gen" gen]                          (cons [:aset] gen)))
    (def #_"gen" Gen''create  (λ [#_"gen" gen, #_"FnExpr" fun]          (cons [:create fun] gen)))
    (def #_"gen" Gen''dup     (λ [#_"gen" gen]                          (cons [:dup] gen)))
    (def #_"gen" Gen''get     (λ [#_"gen" gen, #_"Symbol" name]         (cons [:get name] gen)))
    (def #_"gen" Gen''goto    (λ [#_"gen" gen, #_"label" label]         (cons [:goto label] gen)))
    (def #_"gen" Gen''if-eq?  (λ [#_"gen" gen, #_"label" label]         (cons [:if-eq? label] gen)))
    (def #_"gen" Gen''if-nil? (λ [#_"gen" gen, #_"label" label]         (cons [:if-nil? label] gen)))
    (def #_"gen" Gen''invoke  (λ [#_"gen" gen, #_"fn" f, #_"int" arity] (cons [(-/keyword (str "invoke" \- arity)) f] gen)))
    (def #_"gen" Gen''load    (λ [#_"gen" gen, #_"int" index]           (cons [:load index] gen)))
    (def #_"gen" Gen''pop     (λ [#_"gen" gen]                          (cons [:pop] gen)))
    (def #_"gen" Gen''push    (λ [#_"gen" gen, #_"value" value]         (cons [:push value] gen)))
    (def #_"gen" Gen''return  (λ [#_"gen" gen]                          (cons [:return] gen)))
    (def #_"gen" Gen''store   (λ [#_"gen" gen, #_"int" index]           (cons [:store index] gen)))
)

(-/about #_"Compiler"
    (def #_"int" Compiler'MAX_POSITIONAL_ARITY #_9 (+ 9 2))

    (def #_"Namespace" Compiler'namespaceFor (λ [#_"Namespace" inns, #_"Symbol" sym]
        (-/let [#_"Symbol" nsSym (symbol (get sym :ns))]
            (-/or (Namespace''getAlias inns, nsSym) (Namespace'find nsSym))
        )
    ))

    (def #_"Var" Compiler'lookupVar (λ [#_"Symbol" sym, #_"boolean" intern?]
        (-/let [sym (symbol! sym)]
            (-/cond
                (some? (get sym :ns))
                    (-/when-some [#_"Namespace" ns (Compiler'namespaceFor Beagle'repl, sym)]
                        (-/let [#_"Symbol" name (symbol (get sym :name))]
                            (if (-/and intern? (= ns Beagle'repl))
                                (Namespace''intern ns, name)
                                (Namespace''findInternedVar ns, name)
                            )
                        )
                    )
                :else
                    (-/let [#_"Object" o (Namespace''getMapping Beagle'repl, sym)]
                        (-/cond
                            (nil? o)
                                (-/when intern?
                                    (Namespace''intern Beagle'repl, (symbol (get sym :name)))
                                )
                            (var? o)
                                o
                            :else
                                (-/throw! (str "expecting var, but " sym " is mapped to " o))
                        )
                    )
            )
        )
    ))

    (def #_"Var" Compiler'maybeMacro (λ [#_"Object" op, #_"map" scope]
        (-/when-not (-/and (symbol? op) (some? (get (deref (get scope :'local-env)) op)))
            (-/when (-/or (symbol? op) (var? op))
                (-/let [#_"Var" v (if (var? op) op (Compiler'lookupVar op, false))]
                    (-/when (-/and (some? v) (get (meta v) :macro))
                        v
                    )
                )
            )
        )
    ))

    (def #_"Object" Compiler'resolveIn (λ [#_"Namespace" n, #_"Symbol" sym]
        (-/let [sym (symbol! sym)]
            (-/cond
                (some? (get sym :ns))
                    (-/when-some [#_"Namespace" ns (Compiler'namespaceFor n, sym)]                     => (-/throw! (str "no such namespace: " (get sym :ns)))
                        (-/when-some [#_"Var" v (Namespace''findInternedVar ns, (symbol (get sym :name)))] => (-/throw! (str "no such var: " sym))
                            v
                        )
                    )
                :else
                    (-/or (Namespace''getMapping n, sym) (-/throw! (str "unable to resolve symbol: " sym " in this context")))
            )
        )
    ))

    (def #_"gen" Compiler'emitArgs (λ [#_"map" scope, #_"gen" gen, #_"Expr*" args]
        (-/let [
            gen (Gen''push gen, (count args))
            gen (Gen''anew gen)
        ]
            (-/loop-when [gen gen #_"int" i 0 #_"seq" s (seq args)] (some? s) => gen
                (-/let [
                    gen (Gen''dup gen)
                    gen (Gen''push gen, i)
                    gen (Expr'''emit (first s), :Context'EXPRESSION, scope, gen)
                    gen (Gen''aset gen)
                ]
                    (recur gen (inc i) (next s))
                )
            )
        )
    ))

    (-/declare FnMethod''emitLocal)

    (def #_"gen" Compiler'emitLocals (λ [#_"map" scope, #_"gen" gen, #_"map" locals]
        (-/let [
            gen (Gen''push gen, (<< (count locals) 1))
            gen (Gen''anew gen)
        ]
            (-/loop-when [gen gen #_"int" i 0 #_"seq" s (vals locals)] (some? s) => gen
                (-/let [
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
    (-/defr LiteralExpr)

    (def #_"LiteralExpr" LiteralExpr'new (λ [#_"Object" value]
        (-/new* LiteralExpr'class
            (-/array-map
                #_"Object" :value value
            )
        )
    ))

    (def #_"LiteralExpr" LiteralExpr'NIL   (LiteralExpr'new nil))
    (def #_"LiteralExpr" LiteralExpr'TRUE  (LiteralExpr'new true))
    (def #_"LiteralExpr" LiteralExpr'FALSE (LiteralExpr'new false))

    (def #_"Expr" LiteralExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [#_"int" n (dec (count form))]
            (-/when (= n 1) => (-/throw! (str "wrong number of arguments passed to quote: " n))
                (-/let [#_"Object" x (second form)]
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

    (-/defm LiteralExpr Expr
        (Expr'''emit => LiteralExpr''emit)
    )
)

(-/about #_"UnresolvedVarExpr"
    (-/defr UnresolvedVarExpr)

    (def #_"UnresolvedVarExpr" UnresolvedVarExpr'new (λ [#_"Symbol" symbol]
        (-/new* UnresolvedVarExpr'class
            (-/array-map
                #_"Symbol" :symbol symbol
            )
        )
    ))

    (def #_"gen" UnresolvedVarExpr''emit (λ [#_"UnresolvedVarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        gen
    ))

    (-/defm UnresolvedVarExpr Expr
        (Expr'''emit => UnresolvedVarExpr''emit)
    )
)

(-/about #_"VarExpr"
    (-/defr VarExpr)

    (def #_"VarExpr" VarExpr'new (λ [#_"Var" var]
        (-/new* VarExpr'class
            (-/array-map
                #_"Var" :var var
            )
        )
    ))

    (def #_"gen" VarExpr''emit (λ [#_"VarExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/let [
            gen (Gen''push gen, (get this :var))
            gen (Gen''invoke gen, var-get, 1)
        ]
            (-/when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    ))

    (-/defm VarExpr Expr
        (Expr'''emit => VarExpr''emit)
    )
)

(-/about #_"BodyExpr"
    (-/defr BodyExpr)

    (def #_"BodyExpr" BodyExpr'new (λ [#_"Expr*" exprs]
        (-/new* BodyExpr'class
            (-/array-map
                #_"Expr*" :exprs exprs
            )
        )
    ))

    (-/declare Compiler'analyze)

    (def #_"Expr" BodyExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [#_"seq" s form s (if (= (first s) 'do) (next s) s)
              #_"Expr*" z
                (-/loop-when [z nil s s] (some? s) => (reverse z)
                    (-/let [#_"Context" c (if (-/or (= context :Context'STATEMENT) (some? (next s))) :Context'STATEMENT context)]
                        (recur (cons (Compiler'analyze (first s), c, scope) z) (next s))
                    )
                )]
            (BodyExpr'new (-/or (seq z) (list LiteralExpr'NIL)))
        )
    ))

    (def #_"gen" BodyExpr''emit (λ [#_"BodyExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/loop-when-recur [gen gen #_"seq" s (seq (get this :exprs))]
                         (some? (next s))
                         [(Expr'''emit (first s), :Context'STATEMENT, scope, gen) (next s)]
                      => (Expr'''emit (first s), context, scope, gen)
        )
    ))

    (-/defm BodyExpr Expr
        (Expr'''emit => BodyExpr''emit)
    )
)

(-/about #_"IfExpr"
    (-/defr IfExpr)

    (def #_"IfExpr" IfExpr'new (λ [#_"Expr" test, #_"Expr" then, #_"Expr" else]
        (-/new* IfExpr'class
            (-/array-map
                #_"Expr" :test test
                #_"Expr" :then then
                #_"Expr" :else else
            )
        )
    ))

    (def #_"Expr" IfExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/cond
            (< 4 (count form)) (-/throw! "too many arguments to if")
            (< (count form) 3) (-/throw! "too few arguments to if")
        )
        (-/let [
            #_"Expr" test (Compiler'analyze (second form), :Context'EXPRESSION, scope)
            #_"Expr" then (Compiler'analyze (third form), context, scope)
            #_"Expr" else (Compiler'analyze (fourth form), context, scope)
        ]
            (IfExpr'new test, then, else)
        )
    ))

    (def #_"gen" IfExpr''emit (λ [#_"IfExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/let [
            #_"label" l'nil (Gen''label gen) #_"label" l'false (Gen''label gen) #_"label" l'end (Gen''label gen)
            gen (Expr'''emit (get this :test), :Context'EXPRESSION, scope, gen)
            gen (Gen''dup gen)
            gen (Gen''if-nil? gen, l'nil)
            gen (Gen''push gen, false)
            gen (Gen''if-eq? gen, l'false)
            gen (Expr'''emit (get this :then), context, scope, gen)
            gen (Gen''goto gen, l'end)
            gen (Gen''mark gen, l'nil)
            gen (Gen''pop gen)
            gen (Gen''mark gen, l'false)
            gen (Expr'''emit (get this :else), context, scope, gen)
            gen (Gen''mark gen, l'end)
        ]
            gen
        )
    ))

    (-/defm IfExpr Expr
        (Expr'''emit => IfExpr''emit)
    )
)

(-/about #_"InvokeExpr"
    (-/defr InvokeExpr)

    (def #_"InvokeExpr" InvokeExpr'new (λ [#_"Expr" fexpr, #_"Expr*" args]
        (-/new* InvokeExpr'class
            (-/array-map
                #_"Expr" :fexpr fexpr
                #_"Expr*" :args args
            )
        )
    ))

    (def #_"Expr" InvokeExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [
            #_"Expr" fexpr (Compiler'analyze (first form), :Context'EXPRESSION, scope)
            #_"Expr*" args (doall (map (λ [%] (Compiler'analyze %, :Context'EXPRESSION, scope)) (next form)))
        ]
            (InvokeExpr'new fexpr, args)
        )
    ))

    (def #_"gen" InvokeExpr''emit (λ [#_"InvokeExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/let [
            gen (Expr'''emit (get this :fexpr), :Context'EXPRESSION, scope, gen)
            gen (Compiler'emitArgs scope, gen, (get this :args))
            gen (Gen''apply gen)
        ]
            (-/when (= context :Context'STATEMENT) => gen
                (Gen''pop gen)
            )
        )
    ))

    (-/defm InvokeExpr Expr
        (Expr'''emit => InvokeExpr''emit)
    )
)

(-/let [last-uid' (atom 0)] (def next-uid! (λ [] (swap! last-uid' inc))))

(-/about #_"LocalBinding"
    (-/defr LocalBinding)

    (def #_"LocalBinding" LocalBinding'new (λ [#_"Symbol" sym, #_"Expr" init, #_"int" idx]
        (-/new* LocalBinding'class
            (-/array-map
                #_"int" :uid (next-uid!)
                #_"Symbol" :sym sym
                #_"Expr'" :'init (atom init)
                #_"int" :idx idx
            )
        )
    ))
)

(-/about #_"LocalBindingExpr"
    (-/defr LocalBindingExpr)

    (def #_"LocalBindingExpr" LocalBindingExpr'new (λ [#_"LocalBinding" lb]
        (-/new* LocalBindingExpr'class
            (-/array-map
                #_"LocalBinding" :lb lb
            )
        )
    ))

    (def #_"gen" LocalBindingExpr''emit (λ [#_"LocalBindingExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-not (= context :Context'STATEMENT) => gen
            (FnMethod''emitLocal (get scope :fm), gen, (get this :lb))
        )
    ))

    (-/defm LocalBindingExpr Expr
        (Expr'''emit => LocalBindingExpr''emit)
    )
)

(-/about #_"FnMethod"
    (-/defr FnMethod)

    (def #_"FnMethod" FnMethod'new (λ [#_"FnExpr" fun, #_"FnMethod" parent]
        (-/new* FnMethod'class
            (-/array-map
                #_"FnExpr" :fun fun
                #_"FnMethod" :parent parent
                #_"{int LocalBinding}'" :'locals (atom (-/array-map))
                #_"Integer" :arity nil
                #_"Expr" :body nil
            )
        )
    ))

    (def #_"FnMethod" FnMethod'parse (λ [#_"FnExpr" fun, #_"seq" form, #_"map" scope]
        (-/let [
            scope (update scope :fm (λ [%] (FnMethod'new fun %)))
            scope (update scope :'local-env (comp atom deref))
            scope (assoc scope :'local-num (atom 0))
            _
                (-/when-some [#_"Symbol" f (get fun :fname)]
                    (-/let [#_"LocalBinding" lb (LocalBinding'new f, nil, (deref (get scope :'local-num)))]
                        (swap! (get scope :'local-env) assoc (get lb :sym) lb)
                        (swap! (get (get scope :fm) :'locals) assoc (get lb :uid) lb)
                    )
                )
            [#_"LocalBinding*" lbs #_"int" arity]
                (-/loop-when [lbs nil arity 0 #_"boolean" variadic? false #_"seq" s (seq (first form))] (some? s) => (if (-/and variadic? (not (neg? arity))) (-/throw! "missing variadic parameter") [(reverse lbs) arity])
                    (-/let [#_"symbol?" sym (first s)]
                        (-/when (symbol? sym)        => (-/throw! "function parameters must be symbols")
                            (-/when (nil? (get sym :ns)) => (-/throw! (str "can't use qualified name as parameter: " sym))
                                (-/cond
                                    (= sym '&)
                                        (-/when-not variadic? => (-/throw! "overkill variadic parameter list")
                                            (recur lbs arity true (next s))
                                        )
                                    (neg? arity)
                                        (-/throw! (str "excess variadic parameter: " sym))
                                    ((if variadic? <= <) arity Compiler'MAX_POSITIONAL_ARITY)
                                        (-/let [
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
            scope (assoc scope :loop-locals lbs)
            scope (update scope :fm (λ [%] (assoc % :arity arity)))
        ]
            (assoc (get scope :fm) :body (BodyExpr'parse (next form), :Context'RETURN, scope))
        )
    ))

    (def #_"gen" FnMethod''emitLocal (λ [#_"FnMethod" this, #_"gen" gen, #_"LocalBinding" lb]
        (if (contains? (deref (get (get this :fun) :'closes)) (get lb :uid))
            (-/let [
                gen (Gen''load gen, 0)
                gen (Gen''get gen, (get lb :sym))
            ]
                gen
            )
            (Gen''load gen, (get lb :idx))
        )
    ))

    (def #_"code" FnMethod''compile (λ [#_"FnMethod" this]
        (-/let [
            #_"map" scope (-/array-map :fm this)
            #_"gen" gen (Gen'new)
            scope (assoc scope :loop-label (Gen''mark gen))
            gen (Expr'''emit (get this :body), :Context'RETURN, scope, gen)
            gen (Gen''return gen)
        ]
            (-/vec (reverse gen))
        )
    ))
)

(-/about #_"FnExpr"
    (-/defr FnExpr)

    (def #_"FnExpr" FnExpr'new (λ []
        (-/new* FnExpr'class
            (-/array-map
                #_"Symbol" :fname nil
                #_"{int FnMethod}" :regulars nil
                #_"FnMethod" :variadic nil
                #_"{int LocalBinding}'" :'closes (atom (-/array-map))
            )
        )
    ))

    (def #_"Expr" FnExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [
            #_"FnExpr" fun (FnExpr'new)
            [fun form]
                (-/when (symbol? (second form)) => [fun form]
                    [(assoc fun :fname (second form)) (cons (symbol! 'fn*) (next (next form)))]
                )
            form
                (-/when (vector? (second form)) => form
                    (list (symbol! 'fn*) (next form))
                )
            [#_"{int FnMethod}" regulars #_"FnMethod" variadic]
                (-/loop-when [regulars (-/array-map) variadic nil #_"seq" s (next form)] (some? s) => [regulars variadic]
                    (-/let [#_"FnMethod" fm (FnMethod'parse fun, (first s), scope) #_"int" n (get fm :arity)]
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
            (-/let [
                gen (Compiler'emitLocals scope, gen, (deref (get this :'closes)))
                gen (Gen''invoke gen, RT'mapUniqueKeys, 1)
            ]
                (Gen''create gen, this)
            )
        )
    ))

    (-/defm FnExpr Expr
        (Expr'''emit => FnExpr''emit)
    )
)

(-/about #_"DefExpr"
    (-/defr DefExpr)

    (def #_"DefExpr" DefExpr'new (λ [#_"Var" var, #_"Expr" init, #_"boolean" initProvided]
        (-/new* DefExpr'class
            (-/array-map
                #_"Var" :var var
                #_"Expr" :init init
                #_"boolean" :initProvided initProvided
            )
        )
    ))

    (def #_"Expr" DefExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [#_"int" n (count form)]
            (-/cond
                (< 3 n) (-/throw! "too many arguments to def")
                (< n 2) (-/throw! "too few arguments to def")
                :else
                    (-/let-when [#_"symbol?" s (second form)] (symbol? s)     => (-/throw! "first argument to def must be a symbol")
                        (-/when-some [#_"Var" v (Compiler'lookupVar s, true)] => (-/throw! "can't refer to qualified var that doesn't exist")
                            (-/let [v (-/when-not (= (get v :ns) Beagle'repl) => v
                                        (-/when (nil? (get s :ns))                => (-/throw! "can't create defs outside of current ns")
                                            (Namespace''intern Beagle'repl, s)
                                        )
                                    )]
                                (DefExpr'new v, (Compiler'analyze (third form), :Context'EXPRESSION, scope), (= n 3))
                            )
                        )
                    )
            )
        )
    ))

    (def #_"gen" DefExpr''emit (λ [#_"DefExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/let [
            gen (Gen''push gen, (get this :var))
            gen
                (-/when (get this :initProvided) => gen
                    (-/let [
                        gen (Gen''dup gen)
                        gen (Expr'''emit (get this :init), :Context'EXPRESSION, scope, gen)
                        gen (Gen''invoke gen, Var''bindRoot, 2)
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

    (-/defm DefExpr Expr
        (Expr'''emit => DefExpr''emit)
    )
)

(-/about #_"LetExpr"
    (-/defr LetExpr)

    (def #_"LetExpr" LetExpr'new (λ [#_"LocalBinding*" bindings, #_"Expr" body, #_"boolean" loop?]
        (-/new* LetExpr'class
            (-/array-map
                #_"LocalBinding*" :bindings bindings
                #_"Expr" :body body
                #_"boolean" :loop? loop?
            )
        )
    ))

    (def #_"Expr" LetExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let [#_"vector?" bindings (second form)]
            (-/when (vector? bindings)                 => (-/throw! "bad binding form, expected vector")
                (-/when (zero? (& (count bindings) 1)) => (-/throw! "bad binding form, expected matched symbol expression pairs")
                    (-/let [
                        scope (update scope :'local-env (comp atom deref))
                        scope (update scope :'local-num (comp atom deref))
                        #_"boolean" loop? (= (first form) 'loop*)
                        scope
                            (-/when loop? => scope
                                (dissoc scope :loop-locals)
                            )
                        #_"LocalBinding*" lbs
                            (-/loop-when [lbs nil #_"seq" s (seq bindings)] (some? s) => (reverse lbs)
                                (-/let [#_"symbol?" sym (first s)]
                                    (-/when (symbol? sym)        => (-/throw! (str "bad binding form, expected symbol, got: " sym))
                                        (-/when (nil? (get sym :ns)) => (-/throw! (str "can't let qualified name: " sym))
                                            (-/let [
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
        (-/let [
            gen
                (-/loop-when [gen gen #_"seq" s (seq (get this :bindings))] (some? s) => gen
                    (-/let [
                        #_"LocalBinding" lb (first s)
                        gen (Expr'''emit (deref (get lb :'init)), :Context'EXPRESSION, scope, gen)
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
            (Expr'''emit (get this :body), context, scope, gen)
        )
    ))

    (-/defm LetExpr Expr
        (Expr'''emit => LetExpr''emit)
    )
)

(-/about #_"RecurExpr"
    (-/defr RecurExpr)

    (def #_"RecurExpr" RecurExpr'new (λ [#_"LocalBinding*" loopLocals, #_"Expr*" args]
        (-/new* RecurExpr'class
            (-/array-map
                #_"LocalBinding*" :loopLocals loopLocals
                #_"Expr*" :args args
            )
        )
    ))

    (def #_"Expr" RecurExpr'parse (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/when (-/and (= context :Context'RETURN) (contains? scope :loop-locals)) => (-/throw! "can only recur from tail position")
            (-/let [#_"Expr*" args (doall (map (λ [%] (Compiler'analyze %, :Context'EXPRESSION, scope)) (next form))) #_"int" n (count args) #_"int" m (count (get scope :loop-locals))]
                (-/when (= n m) => (-/throw! (str "mismatched argument count to recur, expected: " m " args, got: " n))
                    (RecurExpr'new (get scope :loop-locals), args)
                )
            )
        )
    ))

    (def #_"gen" RecurExpr''emit (λ [#_"RecurExpr" this, #_"Context" context, #_"map" scope, #_"gen" gen]
        (-/when-some [#_"label" l'loop (get scope :loop-label)] => (-/throw! "recur misses loop label")
            (-/let [
                gen
                    (-/loop-when-recur [gen gen #_"seq" s (seq (get this :args))]
                                     (some? s)
                                     [(Expr'''emit (first s), :Context'EXPRESSION, scope, gen) (next s)]
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

    (-/defm RecurExpr Expr
        (Expr'''emit => RecurExpr''emit)
    )
)

(-/about #_"Compiler"
    (def #_"map" Compiler'specials
        (-/array-map
            '&          nil
            'def        DefExpr'parse
            'do         BodyExpr'parse
            'fn*        FnExpr'parse        'λ      FnExpr'parse
            'if         IfExpr'parse
            'let*       LetExpr'parse
            'loop*      LetExpr'parse
            'quote      LiteralExpr'parse
            'recur      RecurExpr'parse
        )
    )

    (def #_"boolean" Compiler'isSpecial (λ [#_"Object" sym]
        (contains? Compiler'specials sym)
    ))

    (def #_"edn" Compiler'macroexpand1 (λ [#_"edn" form, #_"map" scope]
        (-/when (seq? form) => form
            (-/let-when [#_"Object" op (first form)] (not (Compiler'isSpecial op)) => form
                (-/let-when [#_"Var" v (Compiler'maybeMacro op, scope)] (some? v) => form
                    (apply v form (deref (get scope :'local-env)) (next form))
                )
            )
        )
    ))

    (def #_"edn" Compiler'macroexpand (λ [#_"edn" form, #_"map" scope]
        (-/let-when [#_"edn" f (Compiler'macroexpand1 form, scope)] (identical? f form) => (recur f, scope)
            form
        )
    ))

    (def #_"void" Compiler'closeOver (λ [#_"LocalBinding" lb, #_"FnMethod" fm]
        (-/when (-/and (some? lb) (some? fm) (not (contains? (deref (get fm :'locals)) (get lb :uid))))
            (swap! (get (get fm :fun) :'closes) assoc (get lb :uid) lb)
            (Compiler'closeOver lb, (get fm :parent))
        )
        nil
    ))

    (def #_"Expr" Compiler'analyzeSymbol (λ [#_"Symbol" sym, #_"map" scope]
        (-/or
            (-/when (nil? (get sym :ns))
                (-/when-some [#_"LocalBinding" lb (get (deref (get scope :'local-env)) sym)]
                    (Compiler'closeOver lb, (get scope :fm))
                    (LocalBindingExpr'new lb)
                )
            )
            (-/let [#_"Object" o (Compiler'resolveIn Beagle'repl, sym)]
                (-/cond
                    (var? o)
                        (-/when (nil? (Compiler'maybeMacro o, scope)) => (-/throw! (str "can't take value of a macro: " o))
                            (VarExpr'new o)
                        )
                    (symbol? o)
                        (UnresolvedVarExpr'new o)
                    :else
                        (-/throw! (str "unable to resolve symbol: " sym " in this context"))
                )
            )
        )
    ))

    (def #_"Expr" Compiler'analyzeSeq (λ [#_"seq" form, #_"Context" context, #_"map" scope]
        (-/let-when [#_"Object" me (Compiler'macroexpand1 form, scope)] (= me form) => (Compiler'analyze me, context, scope)
            (-/when-some [#_"Object" op (first form)] => (-/throw! (str "can't call nil, form: " form))
                (-/let [#_"fn" f'parse (-/or (get Compiler'specials op) InvokeExpr'parse)]
                    (f'parse form, context, scope)
                )
            )
        )
    ))

    (def #_"Expr" Compiler'analyze (λ [#_"edn" form, #_"Context" context, #_"map" scope]
        (-/let [form
                (-/when (lazy-seq? form) => form
                    (-/or (seq form) (list))
                )]
            (-/cond
                (= form nil)                      LiteralExpr'NIL
                (= form true)                     LiteralExpr'TRUE
                (= form false)                    LiteralExpr'FALSE
                (symbol? form)                   (Compiler'analyzeSymbol form, scope)
                (-/and (-/or (seq? form) (map? form) (vector? form)) (empty? form)) (LiteralExpr'new form)
                (seq? form)                      (Compiler'analyzeSeq form, context, scope)
                :else                            (LiteralExpr'new form)
            )
        )
    ))

    (def #_"edn" Compiler'eval (λ [#_"edn" form, #_"map" scope]
        (-/let [form (Compiler'macroexpand form, scope)]
            (IFn'''applyTo (Closure'new (Compiler'analyze (list (symbol! 'fn*) [] form), :Context'EXPRESSION, scope), nil), nil)
        )
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
        (not= (Character'digit ch, base) -1)
    ))

    (def #_"boolean" LispReader'isWhitespace (λ [#_"char" ch]
        (-/or (Character'isWhitespace ch) (= ch \,))
    ))

    (def #_"Character" LispReader'read1 (λ [#_"Reader" r]
        (-/let [#_"int" c (Reader''read r)]
            (-/when-not (= c -1)
                (-/char c)
            )
        )
    ))

    (def #_"void" LispReader'unread (λ [#_"PushbackReader" r, #_"Character" ch]
        (-/when (some? ch)
            (PushbackReader''unread r, (-/int ch))
        )
        nil
    ))

    (def #_"Pattern" LispReader'rxInteger (Pattern'compile "[-+]?(?:0|[1-9][0-9]*)"))

    (def #_"Object" LispReader'matchNumber (λ [#_"String" s]
        (-/let-when [#_"Matcher" m (Pattern''matcher LispReader'rxInteger, s)] (Matcher''matches m)
            (Integer'parseInt s)
        )
    ))

    (def #_"Object" LispReader'readNumber (λ [#_"PushbackReader" r, #_"char" ch]
        (-/let [#_"String" s
                (-/let [#_"StringBuilder" sb (StringBuilder'new) _ (StringBuilder''append sb, ch)]
                    (-/loop []
                        (-/let [ch (LispReader'read1 r)]
                            (if (-/or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isMacro ch))
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
            (-/or (LispReader'matchNumber s) (-/throw! (str "invalid number: " s)))
        )
    ))

    (def #_"String" LispReader'readToken (λ [#_"PushbackReader" r, #_"char" ch]
        (-/let [#_"StringBuilder" sb (StringBuilder'new) _ (StringBuilder''append sb, ch)]
            (-/loop []
                (-/let [ch (LispReader'read1 r)]
                    (if (-/or (nil? ch) (LispReader'isWhitespace ch) (LispReader'isTerminatingMacro ch))
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
    ))

    (def #_"Pattern" LispReader'rxSymbol (Pattern'compile ":?(?:[-a-zA-Z_][-a-zA-Z_0-9.]*/)?[-a-zA-Z_*?!<=>&%λ][-a-zA-Z_*?!<=>0-9'#]*"))

    (def #_"Object" LispReader'matchSymbol (λ [#_"String" s]
        (-/let-when [#_"Matcher" m (Pattern''matcher LispReader'rxSymbol, s)] (Matcher''matches m)
            (-/let [#_"boolean" kw? (= (String''charAt s, 0) \:) #_"Symbol" sym (symbol (String''substring s, (if kw? 1 0)))]
                (if kw? (keyword sym) sym)
            )
        )
    ))

    (def #_"Object" LispReader'interpretToken (λ [#_"String" s]
        (-/cond (= s "nil") nil (= s "true") true (= s "false") false :else
            (-/or (LispReader'matchSymbol s) (-/throw! (str "invalid token: " s)))
        )
    ))

    (def #_"Object" LispReader'read (λ [#_"PushbackReader" r, #_"map" scope, #_"Character" delim]
        (-/loop []
            (-/let [#_"char" ch (-/loop-when-recur [ch (LispReader'read1 r)] (-/and (some? ch) (LispReader'isWhitespace ch)) [(LispReader'read1 r)] => ch)]
                (-/cond
                    (nil? ch)
                        (-/throw! "EOF while reading")
                    (-/and (some? delim) (= delim ch))
                        delim
                    (LispReader'isDigit ch, 10)
                        (LispReader'readNumber r, ch)
                    :else
                        (-/let [#_"fn" f'macro (get LispReader'macros ch)]
                            (if (some? f'macro)
                                (-/let [#_"Object" o (f'macro r scope ch)]
                                    (-/recur-when (identical? o r) [] => o)
                                )
                                (-/or
                                    (-/when (-/or (= ch \+) (= ch \-))
                                        (-/let [#_"char" ch' (LispReader'read1 r) _ (LispReader'unread r, ch')]
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
        (-/loop [#_"seq" z nil]
            (-/let [#_"Object" form (LispReader'read r, scope, delim)]
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
        (-/let [#_"StringBuilder" sb (StringBuilder'new)]
            (-/loop []
                (-/when-some [#_"char" ch (LispReader'read1 r)] => (-/throw! "EOF while reading string")
                    (-/when-not (= ch \") ;; oops! "
                        (StringBuilder''append sb, (if (= ch \\) (StringReader'escape r) ch))
                        (recur)
                    )
                )
            )
            (StringBuilder''toString sb)
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
            (-/let [#_"String" token (LispReader'readToken r, ch)]
                (-/when-not (= (String''length token) 1) => (Character'valueOf (String''charAt token, 0))
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
        (-/array-map
            \"  string-reader ;; oops! "
            \'  quote-reader    \`  quote-reader
            \(  list-reader,    \)  unmatched-delimiter-reader
            \[  vector-reader,  \]  unmatched-delimiter-reader
            \\  character-reader
            \#  dispatch-reader
        )
    )

    (def #_"{char fn}" LispReader'dispatchMacros
        (-/array-map
            \_  discard-reader
        )
    )
)

(def read (λ [] (LispReader'read System'in, nil, nil)))
)

(-/about #_"Beagle"

(-/about #_"Beagle'repl"
    (swap! Namespace'namespaces assoc 'clojure.core (-/the-ns 'clojure.core))
    (swap! Namespace'namespaces assoc 'beagle.bore (-/the-ns 'beagle.bore))
    (swap! Namespace'namespaces assoc 'beagle.core (-/the-ns 'beagle.core))

    (def #_"Var" Beagle'repl (create-ns (symbol "beagle.repl")))

    (alias (symbol "-"), (-/the-ns 'beagle.core))
)

(def repl (λ []
    (-/let [#_"map" scope (-/array-map :'local-env (atom (-/array-map)))]
        (-/loop []
            (print "\033[31mBeagle \033[32m=> \033[0m")
            (flush)
            (prn (Compiler'eval (read) scope))
            (recur)
        )
    )
))
)
