/*  The word operations' pinned terms and the constructors they read,
 *  printed by lean/Words.lean, which proves each operation computes its
 *  function on every input (AvonWords.add_spec .. rem_spec, len_spec ..
 *  drop_spec, beq_spec, bget_spec, ideq_spec) and the C's fires sound
 *  (fireC_num, fireC_arg, listFireC_sound, beq_fire, bget_fire,
 *  ideq_fire).  Generated; do not edit. */

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

#define AV_PIN_LEN \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S I (K K)))) (S (K K" \
    ") (S (K K) (S (K (S (K K) (S (K (S I)) K)))))))"

#define AV_PIN_AT \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K K) S))" \
    ")) (S (K K) (S (K (S (S (K S) (S (K K) (S (K S) (S (K (S (K S))) (S (K K" \
    ")))))))) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) (S (S (" \
    "K S) (S (K (S (K S))) (S (K (S (K K))) (S (K S))))) (K (K K)))))) (K K))" \
    ")))))"

#define AV_PIN_APP \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S S)) (S (K K) (S (K (S" \
    " (K (S (S (K S) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) " \
    "(S (K (S I)) K)))) (K K))))))))) (S (K (S (K K))) (S (S (K S) (S (K K) S" \
    ")) (K K))))))"

#define AV_PIN_TAKE \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K K))))))" \
    " (S (K (S (K K))) (S (K (S (S (K S) (S (K K) (S I (K K)))))) (S (K K) (S" \
    " (K (S (K (S (S (K S) (S (K K) (S (K (S (K K))) (S (S (K S) (S (K K) (S " \
    "(K S) (S (K (S I)) K)))) (K K))))))))) (S (K (S (K K))) (S (S (K S) (S (" \
    "K K) S)) (K K))))))))"

#define AV_PIN_DROP \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (S (K S) (S (K (S I))" \
    " K)))) (S (K (S (K K))) (S (K (S (S (K S) (S (K K) (S I (K K)))))) (S (K" \
    " K) (S (K (S (K K))) (S (S (K S) (S (K K) S)) (K K)))))))"

#define AV_PIN_BEQ \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (S (K S) (S (K (S (K S))) (" \
    "S (K (S (S (K S) (S (S (K S) K) (K (S (S (S I (K K)) (K (K (K I)))) (K (" \
    "K (K I))))))))) (S (K K) (S (S (K S) (S (K (S (K S))) (S (K (S (S (K S) " \
    "(S (K K) (S I (K (K I))))))) (S (K K) I)))) (K (K (K (K (K I)))))))))) (" \
    "S (K K) (S (K (S (S (K S) (S (K K) (S (S I (K (K I))) (K (K (K I))))))))" \
    " (S (K K) I))))"

#define AV_PIN_BGET \
    "S (K (S I I)) (S (S (K S) K) (K (S I I))) (S (K (S (K (S (S I (K (K I)))" \
    ")))) (S (K (S (K K))) (S (K (S (K (S I)))) (S (K (S (K K))) (S (S (K S) " \
    "(S (K (S (K S))) (S (K (S (K (S (K S))))) (S (K (S (K (S (K (S (K S)))))" \
    ")) (S (K (S (K (S (K (S (K K))))))) (S (K (S (S (K S) (S (K (S (K S))) (" \
    "S (K K)))))) (S (K K) (S (K K) (S (S (K S) (S (K K) S)) (K K)))))))))) (" \
    "S (K K) (S (K K) (S (K K) (S (S (K S) (S (K K) S)) (K K))))))))))"

#define AV_PIN_IDEQ \
    "S (S (K S) (S (K K) (S (K (S (K (S I I)) (S (S (K S) K) (K (S I I))) (S " \
    "(S (K S) (S (K (S (K S))) (S (K (S (S (K S) (S (S (K S) K) (K (S (S (S I" \
    " (K K)) (K (K (K I)))) (K (K (K I))))))))) (S (K K) (S (S (K S) (S (K (S" \
    " (K S))) (S (K (S (S (K S) (S (K K) (S I (K (K I))))))) (S (K K) I)))) (" \
    "K (K (K (K (K I)))))))))) (S (K K) (S (K (S (S (K S) (S (K K) (S (S I (K" \
    " (K I))) (K (K (K I)))))))) (S (K K) I)))))) (S (S I (K (K (S (K K) K)))" \
    ") (K I))))) (K (S (S I (K (K (S (K K) K)))) (K I)))"

#define AV_PIN_SUC \
    "S (K K) (S (K (S I)) K)"

#define AV_PIN_CONS \
    "S (K (S (K K))) (S (S (K S) (S (K K) (S (K S) (S (K (S I)) K)))) (K K))"

#define AV_PIN_BN \
    "S (K K) K"

#define AV_PIN_BZ \
    "S (K K) (S (K (S (K K))) (S (K (S I)) K))"

#define AV_PIN_BO \
    "S (K K) (S (K K) (S (K (S I)) K))"

#define AV_PIN_NDT \
    "S (K K) (S (K (S I)) K)"

#define AV_PIN_NDB \
    "S (S (K S) (S (K (S (K S))) (S (K (S (K K))) (S (K (S (K S))) (S (S (K S" \
    ") (S (K K) (S (K S) (S (K (S I)) K)))) (K K)))))) (K (K K))"

#define AV_PIN_IDRAW \
    "S (K (S (K K))) (S (K (S I)) K)"

#define AV_PIN_ID \
    "S (K K) (S (K (S I)) K)"

