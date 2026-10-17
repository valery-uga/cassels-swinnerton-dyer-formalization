import AllCharacteristics.SurjectiveSpecialFiberSmoothPoint
import AllCharacteristics.PowerSeriesPencilFlatness
import AllCharacteristics.OriginalPowerSeriesPencilPointReduction

/-! SOURCE ONLY / UNVERIFIED. Literal Section 6 specified-point frontend:
the SAME original q, SAME extension L/k, SAME mapped pencil, SAME L[[t]]
and L((t)). Relative smoothness and flatness are derived internally. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem prescribedPencilOriginalSmoothPoint_relativeSmooth
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hp0 : p ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus) :
    prescribedPencilOriginalSpecialPoint p g hp hg q (closedPoint L) ∈
      (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg)).smoothLocus := by
  let ρ := prescribedPencilOriginalReductionMap p g hp hg
  letI : IsClosedImmersion ρ :=
    isClosedImmersion_hypersurfaceReductionMap
      (PowerSeries.constantCoeff (R := k))
      (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)
      p hp (prescribedPowerSeriesPencil_constantCoeff p g)
      PowerSeries.constantCoeff_surj
  letI : Flat (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg)) :=
    prescribedPowerSeriesPencil_flat p g hp hg hp0
  have H : IsPullback ρ (hypersurfaceToBase p hp)
      (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg))
      (Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := k)))) :=
    isPullback_hypersurfaceReductionMap
      (PowerSeries.constantCoeff (R := k))
      (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg)
      p hp (prescribedPowerSeriesPencil_constantCoeff p g)
  exact mem_smoothLocus_of_smooth_point_in_surjective_specialFiber
    (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg))
    ρ (hypersurfaceToBase p hp) PowerSeries.constantCoeff PowerSeries.constantCoeff_surj
    H (q (closedPoint L)) hsm

/-- The prescribed original smooth point lifts over exactly L[[t]], with its
original canonical special inclusion as exact reduction. No new smoothness
or coefficient-algebra certificate is a final input. -/
theorem prescribedOriginalSmoothPoint_lift_to_same_powerSeries
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hp0 : p ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus) :
    ∃ s : Spec (.of (PowerSeries L)) ⟶ hypersurface
        (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg),
      s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L))) ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := L))) ≫ s =
        q ≫ prescribedPencilOriginalReductionMap p g hp hg :=
  prescribedPencilOriginalPoint_lift_of_relativeSmooth p g hp hg q hq
    (prescribedPencilOriginalSmoothPoint_relativeSmooth p g hp hg hp0 q hsm)

/-- The same prescribed lift and its actual L((t)) generic point, retaining
both projection squares and the internally proved degree. No separability,
perfectness or infinitude assumption on either coefficient field. -/
theorem prescribedOriginalSmoothPoint_powerLaurent_lift_and_degree
    [Module.Finite k L]
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) (hp0 : p ≠ 0)
    (q : Spec (.of L) ⟶ hypersurface p hp)
    (hq : q ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap k L)))
    (hsm : q (closedPoint L) ∈ (hypersurfaceToBase p hp).smoothLocus) :
    ∃ s : Spec (.of (PowerSeries L)) ⟶ hypersurface
        (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg),
      s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L))) ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := L))) ≫ s =
        q ≫ prescribedPencilOriginalReductionMap p g hp hg ∧
      ∃ y : Spec (.of (LaurentSeries L)) ⟶ prescribedLaurentPencilFiber p g hp hg,
        y ≫ pullback.fst (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
            (prescribedPowerSeriesPencil_homogeneous hp hg))
            (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
          Spec.map (CommRingCat.ofHom
            (algebraMap (PowerSeries L) (LaurentSeries L))) ≫ s ∧
        y ≫ pullback.snd (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
            (prescribedPowerSeriesPencil_homogeneous hp hg))
            (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
          Spec.map (CommRingCat.ofHom (laurentSeriesCoefficientMap (k := k) (L := L))) ∧
        Module.finrank (LaurentSeries k) (LaurentSeries L) = Module.finrank k L :=
  prescribedPowerLaurentPencil_lift_and_degree p g hp hg
    (prescribedPencilOriginalSpecialPoint p g hp hg q)
    (prescribedPencilOriginalSpecialPoint_base p g hp hg q hq)
    (prescribedPencilOriginalSmoothPoint_relativeSmooth p g hp hg hp0 q hsm)

end AllCharacteristics
