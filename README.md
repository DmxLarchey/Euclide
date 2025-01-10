```coq
(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*        Mozilla Public License Version 2.0, MPL-2.0         *)
(**************************************************************)
```

# Euclide et l'irrationalité de ⁿ√k pour k différent de rⁿ

```coq
Definition nth_root_rational n k := ∃ p q, q ≠ 0 ∧ q^n*k = p^n.
Definition nth_root_irrational n k := ¬ nth_root_rational n k.
```

```coq
Theorem nth_root_rational__is_pow n k : nth_root_rational n k → ∃r, k = r^n.
```

```coq
Theorem irrationality_criteria n k : (∃i, i^n < k < (1+i)^n) → nth_root_irrational n k.
```

