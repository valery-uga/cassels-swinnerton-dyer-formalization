import PfaffianDescent.SingleSupportActualDualCoordinates

/-! SOURCE ONLY, UNVERIFIED. Restore the original coordinate order of the
actual supplied-Z extraction. In particular Basis.reindex pi (not pi.symm)
has value b (pi.symm r) at r. The chart and original immersion are retained. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
universe u
variable {k : Type u} [Field k] [PerfectField k]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem singleSupport_actual_original_order_dual_chart_data
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1)) :
    letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
    letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
    letI := AllCharacteristics.pointAlgebra (toBase I) P.1
    (AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8) →
    ∃ j : Fin 4, ∃ (g : ChartRing I j →+* Γ(Z, ⊤))
      (x : Fin 4 → Γ(Z, ⊤))
      (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme I).residueField P.1))
      (b : Basis (Fin 4) k ((scheme I).residueField P.1))
      (v : Fin 4 → (scheme I).residueField P.1)
      (full : Fin 4 ≃ ((scheme I).residueField P.1 →ₐ[k] AlgebraicClosure k)),
      x j = 1 ∧ Function.Surjective (aeval (R := k) x) ∧
      g.comp (chartBaseMap I j) = algebraMap k Γ(Z, ⊤) ∧
      b j = 1 ∧ v j = 0 ∧ v ≠ 0 ∧
      (∀ r, x r = g (chartCoordinate I j r)) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j = Z.isoSpec.inv ≫ i ∧
      (∀ r, eA (x r) = inl (b r) + inr (v r)) := by
  classical
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  intro hZ
  obtain ⟨j, g, x, eA, b, v, pi, full, hxj, hgen, hbase,
    hb0, hv0, hv, hpi, hxg, hpoint, hcoords⟩ :=
    singleSupport_actual_dual_coordinates_without_quadratic_dimension
      I i P hSupport hP hGeom hZ
  let originalB := b.reindex pi
  let originalV : Fin 4 → (scheme I).residueField P.1 := fun r => v (pi.symm r)
  have hActual (r : Fin 4) : eA (x r) = inl (originalB r) + inr (originalV r) := by
    simpa only [Equiv.apply_symm_apply, originalB, Basis.reindex_apply, originalV]
      using hcoords (pi.symm r)
  have hb : originalB j = 1 := by
    have h := congrArg TrivSqZeroExt.fst (hActual j)
    simpa only [hxj, map_one, TrivSqZeroExt.fst_one, TrivSqZeroExt.fst_add,
      TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero] using h.symm
  have hvj : originalV j = 0 := by
    have h := congrArg TrivSqZeroExt.snd (hActual j)
    simpa only [hxj, map_one, TrivSqZeroExt.snd_one, TrivSqZeroExt.snd_add,
      TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] using h.symm
  have hvOrig : originalV ≠ 0 := by
    intro hz
    apply hv
    funext r
    have h := congrFun hz (pi r)
    simpa only [originalV, Equiv.symm_apply_apply, Pi.zero_apply] using h
  exact ⟨j, g, x, eA, originalB, originalV, full, hxj, hgen, hbase,
    hb, hvj, hvOrig, hxg, hpoint, hActual⟩

end PfaffianDescent
