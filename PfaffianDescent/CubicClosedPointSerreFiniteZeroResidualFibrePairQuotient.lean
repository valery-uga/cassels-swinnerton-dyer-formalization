import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeLocalFlat

/-! # The actual zero parameter quotient controls the actual ambient fibre pair -/
noncomputable section
namespace PfaffianDescent
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_artinian_fibre_pair_of_zero_parameter_quotient
    {A B : Type*} [CommRing A] [CommRing B]
    (q : A →+* B) (hq : Function.Surjective q) (a b t : A)
    (hk : RingHom.ker q = Ideal.span ({a, b} : Set A))
    [IsArtinianRing (B ⧸ Ideal.span {q t})] :
    IsArtinianRing ((A ⧸ Ideal.span {t}) ⧸
      Ideal.span ({Ideal.Quotient.mk (Ideal.span {t}) a,
        Ideal.Quotient.mk (Ideal.span {t}) b} : Set (A ⧸ Ideal.span {t}))) := by
  let I := Ideal.span ({a, b} : Set A)
  let J := Ideal.span ({t} : Set A)
  let e : (A ⧸ I) ≃+* B :=
    (Ideal.quotEquivOfEq hk.symm).trans (q.quotientKerEquivOfSurjective hq)
  have he : e.toRingHom.comp (Ideal.Quotient.mk I) = q := by
    ext r
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hq r
  have hmap : Ideal.span {q t} = (J.map (Ideal.Quotient.mk I)).map e.toRingHom := by
    rw [Ideal.map_map, he, show J = Ideal.span {t} from rfl,
      Ideal.map_span, Set.image_singleton]
  let eQ := Ideal.quotientEquiv (J.map (Ideal.Quotient.mk I))
    (Ideal.span {q t}) e hmap
  let eF := (DoubleQuot.quotQuotEquivComm J I).trans eQ
  have hA : IsArtinianRing ((A ⧸ J) ⧸ I.map (Ideal.Quotient.mk J)) :=
    eF.symm.isArtinianRing
  have hpair : I.map (Ideal.Quotient.mk J) = Ideal.span
      ({Ideal.Quotient.mk J a, Ideal.Quotient.mk J b} : Set (A ⧸ J)) := by
    rw [show I = Ideal.span ({a, b} : Set A) from rfl, Ideal.map_span, Set.image_pair]
  exact hpair ▸ hA

end PfaffianDescent
