/*  The numeral operations' pinned terms, printed by lean/Words.lean, which
 *  proves each reduces to its operation's numeral on every input
 *  (AvonWords.add_spec .. rem_spec) and word_fire's values those numerals
 *  (AvonWords.fireC_num, fireC_arg).  Generated; do not edit. */

#define AV_PIN_ADD \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I))" \
    " K)))) (S (K (S (K K))) (S (K (S (K (S (K K) (S (K (S I)) K))))))))"

#define AV_PIN_SUB \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I))" \
    " K)))) (S (K (S (K K))) (S (S (K S) K) (K (S (S I (K K)) (K I))))))"

#define AV_PIN_MUL \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))))))" \
    " (S (K (S (K K))) (S (S (K S) (S (K K) (S (K (S I I)) (S (S (K S) K) (K " \
    "(S I I))) (S (K (S (S (K S) (S (K (S I)) K)))) (S (K (S (K K))) (S (K (S" \
    " (K (S (K K) (S (K (S I)) K))))))))))))))"

#define AV_PIN_IFEQ \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S (K " \
    "S))) (S (K (S (K (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S (K K) (S " \
    "(K S) K))))) (K (S (S (K S) (S (K (S (K S))) (S (K K)))) (K (K K))))))))" \
    ")) (S (K K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K" \
    ")))))))) (S (K K) (S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S" \
    " (K S))) (S (K (S (K (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S (K S)" \
    ")))) (K (S (K K) K)))))))) (K (K (S (K K) K))))))))"

#define AV_PIN_IFLE \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K K) (S " \
    "(K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (K (S (S (K S) (S (K " \
    "K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (S (K S) (S (K " \
    "(S (K S))) (S (K (S (K K))) (S (K (S (K S))) (S (K (S (K (S (K S))))) (S" \
    " (S (K S) (S (K K) (S (K S) (S (K S))))) (K (S (K K) K)))))))) (K (K (S " \
    "(K K) K))))))))"

#define AV_PIN_DIV \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))))))" \
    " (S (K (S (K (S (K K))))) (S (S (K S) (S (K (S (K S))) (S (K (S (S (K S)" \
    " (S (K (S (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (" \
    "S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (K (S (S (" \
    "K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (S (" \
    "K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S (K S))) (S (K (S (K (S (" \
    "K S))))) (S (S (K S) (S (K K) (S (K S) (S (K S))))) (K (S (K K) K)))))))" \
    ") (K (K (S (K K) K))))))))))) K)))) (S (K (S (K (S (K (S (K K) (S (K (S " \
    "I)) K))))))) (S (S (K S) (S (K (S (K S))) (S (S (K S) (S (K K) (S (K S) " \
    "K))) (K (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S " \
    "(K (S I)) K)))) (S (K (S (K K))) (S (S (K S) K) (K (S (S I (K K)) (K I))" \
    "))))))))) (K (K I))))))) (K (K (K K))))))"

#define AV_PIN_REM \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I))" \
    " K)))) (S (K (S (K (S (K K))))) (S (S (K S) (S (K (S (K S))) (S (K (S (S" \
    " (K S) (S (K (S (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (" \
    "K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (S (K (" \
    "S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K)))))))) (S (K K) (" \
    "S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S (K S))) (S (K (S (" \
    "K (S (K S))))) (S (S (K S) (S (K K) (S (K S) (S (K S))))) (K (S (K K) K)" \
    "))))))) (K (K (S (K K) K))))))))))) K)))) (S (S (K S) (S (K (S (K S))) (" \
    "S (S (K S) (S (K K) (S (K S) K))) (K (S (K (S I I)) (S (S (K S) K) (K (S" \
    " I I))) (S (K (S (S (K S) (S (K (S I)) K)))) (S (K (S (K K))) (S (S (K S" \
    ") K) (K (S (S I (K K)) (K I))))))))))) (K (K I)))))) (K K))))"

