(defproject beagle "x.y.z"
    :dependencies [[org.clojure/clojure "1.9.0"]]
    :plugins [[lein-try "0.4.3"]]
;   :global-vars {*warn-on-reflection* true}
    :jvm-opts ["-Xmx6g"]
    :javac-options ["-g"]
    :source-paths ["src"] :java-source-paths ["src"]
;   :main beagle.core
    :aliases {"beagle" ["run" "-m" "beagle.core"]})
