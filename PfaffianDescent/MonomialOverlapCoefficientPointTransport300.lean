import PfaffianDescent.MonomialOverlapCoefficientSymmetry293

noncomputable section
namespace PfaffianDescent
universe u
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B C : Fin n → (Fin m →₀ ℕ)) (kB kC : Fin n)
variable (hkB : B kB = 0) (hkC : C kC = 0)

/-- The whole first-chart datum of292's localized classifier is its original
coefficient-chart datum, with the literal restricted original coefficient map. -/
lemma monomialOverlapClassification_chart300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB →ₐ[R] A) :
    (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A p).val =
      cyclicCoefficientWholeIdealChartEquiv287 (A := A) B kB R hkB
        (p.comp (Algebra.algHom R (UniversalCyclicCoefficientAlgebra282 R m n B kB)
          (MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB))) := by
  apply Subtype.ext
  exact monomialOverlapLocalizationAlgHomEquiv_ideal292 R m n B C kB hkB p

/-- The SAME coefficient map underlying298's geometric transition carries
every actual coefficient point to literal same-ideal reversal. -/
lemma monomialOverlapReverseCoefficient_classifies300
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB →ₐ[R] A) :
    monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC A
        (p.comp (monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB)) =
      monomialWholeIdealOverlapFlip293 B C
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A p) := by
  let L := MonomialOverlapCoefficientAlgebra292 R m n B C kB hkB
  let f := monomialOverlapForwardCoefficientMap293 R m n C B kC kB hkC hkB
  have hidentity : monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB A p =
      monomialWholeIdealChartOverlapMap290 B C kB hkB p.toRingHom
        (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB L (AlgHom.id R L)) := by
    have h := monomialOverlapLocalizationAlgHomEquiv_natural292 R m n B C kB hkB
      (AlgHom.id R L) p
    rw [AlgHom.comp_id] at h
    exact h
  calc
    _ = monomialWholeIdealChartOverlapMap290 C B kC hkC p.toRingHom
        (monomialOverlapLocalizationAlgHomEquiv292 R m n C B kC hkC L f) :=
      monomialOverlapLocalizationAlgHomEquiv_natural292 R m n C B kC hkC f p
    _ = monomialWholeIdealChartOverlapMap290 C B kC hkC p.toRingHom
        (monomialWholeIdealOverlapFlip293 B C
          (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB L
            (AlgHom.id R L))) :=
      congrArg (monomialWholeIdealChartOverlapMap290 C B kC hkC p.toRingHom)
        (monomialOverlapForwardCoefficientMap_classifies293 R m n C B kC kB hkC hkB)
    _ = monomialWholeIdealOverlapFlip293 B C
        (monomialWholeIdealChartOverlapMap290 B C kB hkB p.toRingHom
          (monomialOverlapLocalizationAlgHomEquiv292 R m n B C kB hkB L
            (AlgHom.id R L))) :=
      (monomialWholeIdealOverlapFlip_natural293 B C kB kC hkB hkC p.toRingHom _).symm
    _ = _ := congrArg (monomialWholeIdealOverlapFlip293 B C) hidentity.symm

end PfaffianDescent
