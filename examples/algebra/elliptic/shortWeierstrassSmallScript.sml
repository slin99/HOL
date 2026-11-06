(* ------------------------------------------------------------------------- *)
(* Worked Example: y^2 = x^3 + 1 over GF 5                                    *)
(* ------------------------------------------------------------------------- *)
(*
   Documentation

   A small concrete example of the generic curve and group interfaces.

   Point set and group:
     sw_GF5_curve, sw_GF5_points, sw_GF5_card, sw_GF5_finite_group.
   Scalar multiplication and point order:
     sw_GF5_scalar_six, sw_GF5_order_divides_six, sw_GF5_generator_order.
     The point (2,2) has order six.
*)

Theory shortWeierstrassSmall
Ancestors
  shortWeierstrass shortWeierstrassGroup fieldInstances

Theorem sw_GF5_elements[local]:
  !x.
    x IN (GF 5).carrier <=>
    x = 0 \/ x = 1 \/ x = 2 \/ x = 3 \/ x = 4
Proof
  rw[GF_element] >>
  decide_tac
QED

Theorem sw_GF5_curve:
  ShortWeierstrassCurve (GF 5) 0 1
Proof
  rw[ShortWeierstrassCurve_def, GF_field, groupTheory.PRIME_5, GF_element,
     GF_char, sw_discriminant_def, GF_eval, GF_sum_inv,
     monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_affine_truth_table[local]:
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 0) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 0 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 0 3) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 0 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 1 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 1) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 2 2) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 2 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 2 4) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 3 4) /\
   sw_on_curve (GF 5) 0 1 (ECAffine 4 0) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 1) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 2) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 3) /\
  ~sw_on_curve (GF 5) 0 1 (ECAffine 4 4)
Proof
  rw[sw_on_curve_def, sw_curve_rhs_def, GF_element, GF_eval,
     monoidTheory.monoid_exp_def] >>
  EVAL_TAC
QED

Theorem sw_GF5_affine_points[local]:
  !x y.
    sw_on_curve (GF 5) 0 1 (ECAffine x y) <=>
    (x = 0 /\ y = 1) \/
    (x = 0 /\ y = 4) \/
    (x = 2 /\ y = 2) \/
    (x = 2 /\ y = 3) \/
    (x = 4 /\ y = 0)
Proof
  metis_tac[sw_on_curve_ECAffine, sw_GF5_elements,
            sw_GF5_affine_truth_table]
QED

Theorem sw_GF5_points:
  sw_points (GF 5) 0 1 =
    {ECInfinity;
     ECAffine 0 1;
     ECAffine 0 4;
     ECAffine 2 2;
     ECAffine 2 3;
     ECAffine 4 0}
Proof
  rw[pred_setTheory.EXTENSION, sw_points_member] >>
  Cases_on `x` >-
    simp[] >>
  rw[sw_GF5_affine_points] >>
  simp[]
QED

Theorem sw_GF5_card:
  CARD (sw_points (GF 5) 0 1) = 6
Proof
  rw[sw_GF5_points]
QED

Theorem sw_GF5_finite_group:
  FiniteAbelianGroup (sw_group (GF 5) 0 1)
Proof
  irule short_weierstrass_finite_group >>
  simp[sw_GF5_curve, GF_finite_field, groupTheory.PRIME_5]
QED

Theorem sw_GF5_scalar_six:
  P IN sw_points (GF 5) 0 1 ==>
  (sw_group (GF 5) 0 1).exp P 6 = ECInfinity
Proof
  strip_tac >>
  `FiniteGroup (sw_group (GF 5) 0 1)` by
    metis_tac[sw_GF5_finite_group, groupTheory.FiniteAbelianGroup_def_alt] >>
  MP_TAC (Q.ISPECL [`sw_group (GF 5) 0 1`, `P:num sw_point`]
    groupTheory.finite_group_Fermat) >>
  simp[sw_group_carrier, sw_group_id, sw_GF5_card]
QED

Theorem sw_GF5_order_divides_six:
  P IN sw_points (GF 5) 0 1 ==>
  order (sw_group (GF 5) 0 1) P divides 6
Proof
  strip_tac >>
  `FiniteGroup (sw_group (GF 5) 0 1)` by
    metis_tac[sw_GF5_finite_group, groupTheory.FiniteAbelianGroup_def_alt] >>
  MP_TAC (Q.ISPEC `sw_group (GF 5) 0 1` groupTheory.group_order_divides) >>
  simp[sw_group_carrier, sw_GF5_card] >>
  metis_tac[sw_points_member]
QED

Theorem sw_GF5_prod_inv_witness[local]:
  x < 5 /\ x <> 0 /\ y < 5 /\ (x * y) MOD 5 = 1 ==>
  (GF 5).prod.inv x = y
Proof
  rpt strip_tac >>
  `Field (GF 5)` by simp[GF_field, groupTheory.PRIME_5] >>
  `(GF 5).prod.inv x = (Invertibles (GF 5).prod).inv x` by
    metis_tac[sw_field_prod_inv_eq, GF_eval] >>
  asm_rewrite_tac[] >>
  CONV_TAC SYM_CONV >>
  irule ringTheory.ring_unit_rinv_unique >>
  simp[GSYM fieldTheory.field_nonzero_unit, fieldTheory.field_nonzero_eq,
       GF_eval, fieldTheory.field_is_ring]
QED

Theorem sw_GF5_prod_inv_table[local]:
  (GF 5).prod.inv 1 = 1 /\
  (GF 5).prod.inv 2 = 3 /\
  (GF 5).prod.inv 3 = 2 /\
  (GF 5).prod.inv 4 = 4
Proof
  rpt conj_tac >> irule sw_GF5_prod_inv_witness >> simp[]
QED

Theorem sw_GF5_generator_scalars[local]:
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 1 = ECAffine 2 2 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 2 = ECAffine 0 4 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 3 = ECAffine 4 0 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 4 = ECAffine 0 1 /\
  (sw_group (GF 5) 0 1).exp (ECAffine 2 2) 5 = ECAffine 2 3
Proof
  simp[monoidTheory.monoid_exp_def,
       EVAL ``FUNPOW (f:'a->'a) 1 x``,
       EVAL ``FUNPOW (f:'a->'a) 2 x``,
       EVAL ``FUNPOW (f:'a->'a) 3 x``,
       EVAL ``FUNPOW (f:'a->'a) 4 x``,
       EVAL ``FUNPOW (f:'a->'a) 5 x``,
       sw_group_id, sw_group_op, sw_add_def, sw_slope_def,
       sw_add_x_def, sw_add_y_def, sw_GF5_prod_inv_table,
       GF_eval, GF_sum_inv] >>
  EVAL_TAC
QED

Theorem sw_GF5_generator_order:
  order (sw_group (GF 5) 0 1) (ECAffine 2 2) = 6
Proof
  rw[groupTheory.group_order_thm] >-
    (irule sw_GF5_scalar_six >>
     SIMP_TAC bool_ss [sw_GF5_points, pred_setTheory.IN_INSERT,
                      pred_setTheory.NOT_IN_EMPTY]) >>
  `m = 1 \/ m = 2 \/ m = 3 \/ m = 4 \/ m = 5` by decide_tac >>
  pop_assum strip_assume_tac >>
  fs[sw_GF5_generator_scalars]
QED
