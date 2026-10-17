import PfaffianDescent.ProductDualClosedRankTwoFactorIso
import PfaffianDescent.AmbientTensorNormalizedChartSquare

/-! SOURCE ONLY, UNVERIFIED. Internal restriction consumer. Its product-dual
presentation and ambient square are CONSTRUCTED by the actual Gamma/tensor
factory in the next leaf; they are not final original-Z certificates. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem actualProductDual_component_iso_of_original_support
    {Y : Scheme.{u}}
    (c : Y ⟶ Spec (.of (QuarticNet.FourTangentDualAlgebra K))) [IsClosedImmersion c]
    (q : Spec (.of (QuarticNet.FourTangentDualAlgebra K)) ⟶
      Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion q]
    (r : Fin 4) (p : Proj (homogeneousSubmodule (Fin 4) K))
    (hFactor : (actualProductDualFactor r ≫ q)
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
        (IsLocalRing.closedPoint K)) = p)
    (hSupport : Set.range (c ≫ q) = {p})
    (hRank : AllCharacteristics.finiteSchemeRank (c ≫ actualProductDualToBase) = 2) :
    ∃ e : Y ≅ Spec (.of (DualNumber K)),
      e.hom ≫ actualProductDualFactor r = c ∧
      e.hom ≫ actualProductDualFactor r ≫ q = c ≫ q := by
  have hRange : Set.range c ⊆ Set.range (actualProductDualFactor (K := K) r) := by
    rintro _ ⟨y, rfl⟩
    let z := Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
      (IsLocalRing.closedPoint K)
    refine ⟨z, q.isClosedEmbedding.injective ?_⟩
    have hy : (c ≫ q) y = p := by
      apply Set.mem_singleton_iff.mp
      rw [← hSupport]
      exact Set.mem_range_self y
    exact hFactor.trans hy.symm
  obtain ⟨e, he⟩ := actualProductDual_closed_rankTwo_factor_iso c r hRange hRank
  exact ⟨e, he, by rw [← Category.assoc, he]⟩

/-- Restrict an INTERNALLY constructed whole-scheme product-dual iso to
each SAME supplied rank-two closed component; no component source iso is
assumed. The support permutation is the one already derived from the actual
frame support set. -/
theorem actualProductDual_original_component_presentations
    {Q : Scheme.{u}} (eWhole : Q ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K)))
    (qWhole : Q ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    (qProduct : Spec (.of (QuarticNet.FourTangentDualAlgebra K)) ⟶
      Proj (homogeneousSubmodule (Fin 4) K)) [IsClosedImmersion qProduct]
    (hWhole : eWhole.hom ≫ qProduct = qWhole)
    (hBase : qProduct ≫ ambientToBase = actualProductDualToBase)
    (Y : Fin 4 → Scheme.{u}) (c : ∀ i, Y i ⟶ Q) [∀ i, IsClosedImmersion (c i)]
    (rho : Equiv.Perm (Fin 4))
    (p : Fin 4 → Proj (homogeneousSubmodule (Fin 4) K))
    (hFactor : ∀ r, (actualProductDualFactor r ≫ qProduct)
      (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom)
        (IsLocalRing.closedPoint K)) = p r)
    (hSupport : ∀ i, Set.range (c i ≫ qWhole) = {p (rho i)})
    [∀ i, IsFinite ((c i ≫ qWhole) ≫ ambientToBase)]
    (hRank : ∀ i, AllCharacteristics.finiteSchemeRank
      ((c i ≫ qWhole) ≫ ambientToBase) = 2) :
    ∃ e : ∀ i, Y i ≅ Spec (.of (DualNumber K)),
      (∀ i, (e i).hom ≫ actualProductDualFactor (rho i) = c i ≫ eWhole.hom) ∧
      (∀ i, (e i).hom ≫ actualProductDualFactor (rho i) ≫ qProduct = c i ≫ qWhole) := by
  classical
  have hOne (i : Fin 4) :
      ∃ e : Y i ≅ Spec (.of (DualNumber K)),
        e.hom ≫ actualProductDualFactor (rho i) = c i ≫ eWhole.hom ∧
        e.hom ≫ actualProductDualFactor (rho i) ≫ qProduct = c i ≫ qWhole := by
    let d := c i ≫ eWhole.hom
    letI : IsClosedImmersion d := by dsimp only [d]; infer_instance
    have hD : d ≫ qProduct = c i ≫ qWhole := by
      dsimp only [d]
      rw [Category.assoc, hWhole]
    have hDBase : d ≫ actualProductDualToBase = (c i ≫ qWhole) ≫ ambientToBase := by
      rw [← hBase, ← Category.assoc, hD]
    have hD2 : AllCharacteristics.finiteSchemeRank (d ≫ actualProductDualToBase) = 2 := by
      simpa only [hDBase] using hRank i
    obtain ⟨e, he, hq⟩ := actualProductDual_component_iso_of_original_support
      d qProduct (rho i) (p (rho i)) (hFactor (rho i))
      (by rw [hD]; exact hSupport i) hD2
    exact ⟨e, he, hq.trans hD⟩
  choose e he hq using hOne
  exact ⟨e, he, hq⟩

end PfaffianDescent
