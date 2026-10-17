import AllCharacteristics.FiniteSchemeCycle
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Degree-preserving pushforward of effective zero-cycles

A universally closed morphism sends closed points to closed points. Weighting
by the full residue-field degree gives the usual pushforward on effective
zero-cycles. Its degree is preserved under composition, including inseparable
extensions. In particular a finite algebra point on a separated scheme supplies
an actual effective cycle of the algebra's dimension.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace AllCharacteristics
universe u

/-- Residue degrees satisfy the tower law for composable scheme morphisms.
Mathlib's zero convention for infinite degrees is compatible with this formula. -/
theorem residueDegree_comp
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) (x : X) :
    (i ≫ f).residueDegree x = f.residueDegree (i x) * i.residueDegree x := by
  let a := (f.residueFieldMap (i x)).hom
  let b := (i.residueFieldMap x).hom
  let := a.toAlgebra
  let := b.toAlgebra
  let := (b.comp a).toAlgebra
  have : IsScalarTower (Z.residueField (f (i x))) (Y.residueField (i x))
      (X.residueField x) := IsScalarTower.of_algebraMap_eq' rfl
  unfold Scheme.Hom.residueDegree
  rw [Scheme.residueFieldMap_comp]
  exact (Module.finrank_mul_finrank (Z.residueField (f (i x)))
    (Y.residueField (i x)) (X.residueField x)).symm

/-- A universally closed morphism sends closed points to closed points. -/
def universallyClosedPointMap {X Y : Scheme.{u}} (i : X ⟶ Y) [UniversallyClosed i] :
    closedPoints X → closedPoints Y := fun x ↦
  ⟨i x.1, by
    change IsClosed {i x.1}
    rw [← Set.image_singleton]
    exact i.isClosedMap _ x.2⟩

/-- Pushforward of an effective cycle, with each image weighted by its full
residue-field degree. -/
noncomputable def pushforwardCycle {X Y : Scheme.{u}}
    (i : X ⟶ Y) [UniversallyClosed i] (z : EffectiveZeroCycle X) : EffectiveZeroCycle Y :=
  z.sum (fun x n ↦ Finsupp.single (universallyClosedPointMap i x) (n * i.residueDegree x.1))

/-- Every closed point occurring in a proper pushforward is the image of a
closed point occurring on the source.  We state the slightly weaker range
form, which is the one needed when identifying the cycle carried by a
configuration fiber. -/
theorem pushforwardCycle_support_subset_range
    {X Y : Scheme.{u}} (i : X ⟶ Y) [UniversallyClosed i]
    (z : EffectiveZeroCycle X) :
    ↑(pushforwardCycle i z).support ⊆ Set.range (universallyClosedPointMap i) := by
  classical
  intro y hy
  by_contra hyrange
  have hzero : pushforwardCycle i z y = 0 := by
    unfold pushforwardCycle
    rw [Finsupp.sum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    change (Finsupp.single (universallyClosedPointMap i x)
      (z x * i.residueDegree x.1)) y = 0
    rw [Finsupp.single_apply]
    split_ifs with hxy
    · exact False.elim (hyrange ⟨x, hxy⟩)
    · rfl
  exact (Finsupp.mem_support_iff.mp hy) hzero

/-- Weighted cycle pushforward preserves degree to the final base. -/
theorem degree_pushforwardCycle
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [UniversallyClosed i] (f : Y ⟶ Z)
    (z : EffectiveZeroCycle X) :
    EffectiveZeroCycle.degree f (pushforwardCycle i z) =
      EffectiveZeroCycle.degree (i ≫ f) z := by
  classical
  unfold EffectiveZeroCycle.degree pushforwardCycle
  rw [Finsupp.sum_sum_index (fun _ ↦ zero_mul _) (fun _ n m ↦ add_mul n m _)]
  apply Finsupp.sum_congr
  intro x _
  rw [Finsupp.sum_single_index (zero_mul _)]
  change (z x * i.residueDegree x.1) * f.residueDegree (i x.1) =
    z x * (i ≫ f).residueDegree x.1
  rw [residueDegree_comp]
  ac_rfl

/- The residue-weighted effective pushforward is functorial.  This is the
  effective-cycle counterpart of `signedCyclePushforward_comp`, and lets
  iterated finite fibers be compared with their composite map without
  discarding scheme-theoretic multiplicities. -/
theorem pushforwardCycle_comp
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) [UniversallyClosed i]
    (f : Y ⟶ Z) [UniversallyClosed f] (z : EffectiveZeroCycle X) :
    pushforwardCycle (i ≫ f) z = pushforwardCycle f (pushforwardCycle i z) := by
  classical
  induction z using Finsupp.induction with
  | zero =>
      simp [pushforwardCycle]
  | @single_add x n z hx hn hrec =>
      rw [show pushforwardCycle (i ≫ f) (Finsupp.single x n + z) =
        pushforwardCycle (i ≫ f) (Finsupp.single x n) + pushforwardCycle (i ≫ f) z by
          exact Finsupp.sum_add_index' (fun x => by simp)
            (fun x n m => by simp only [add_mul, Finsupp.single_add])]
      rw [show pushforwardCycle i (Finsupp.single x n + z) =
        pushforwardCycle i (Finsupp.single x n) + pushforwardCycle i z by
          exact Finsupp.sum_add_index' (fun x => by simp)
            (fun x n m => by simp only [add_mul, Finsupp.single_add])]
      have hsplitf : pushforwardCycle f (pushforwardCycle i (Finsupp.single x n) +
          pushforwardCycle i z) =
          pushforwardCycle f (pushforwardCycle i (Finsupp.single x n)) +
            pushforwardCycle f (pushforwardCycle i z) := by
        exact Finsupp.sum_add_index' (fun x => by simp)
          (fun x n m => by simp only [add_mul, Finsupp.single_add])
      rw [hsplitf, hrec]
      congr 1
      rw [show pushforwardCycle (i ≫ f) (Finsupp.single x n) =
        Finsupp.single (universallyClosedPointMap (i ≫ f) x)
          (n * (i ≫ f).residueDegree x.val) by
          unfold pushforwardCycle
          exact Finsupp.sum_single_index (by simp)]
      have hpi : pushforwardCycle i (Finsupp.single x n) =
          Finsupp.single (universallyClosedPointMap i x)
            (n * i.residueDegree x.val) := by
        unfold pushforwardCycle
        exact Finsupp.sum_single_index (by simp)
      rw [hpi]
      rw [show pushforwardCycle f (Finsupp.single (universallyClosedPointMap i x)
          (n * i.residueDegree x.val)) =
        Finsupp.single (universallyClosedPointMap f (universallyClosedPointMap i x))
          ((n * i.residueDegree x.val) * f.residueDegree (i x.val)) by
          unfold pushforwardCycle
          exact Finsupp.sum_single_index (by simp)]
      congr 1
      rw [residueDegree_comp]
      ring

/-- An actual point with values in a finite algebra supplies an effective
zero-cycle of the algebra's dimension on any separated scheme over the field. -/
theorem exists_effectiveZeroCycle_of_finite_algebra_point
    {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsSeparated f]
    (q : Spec (.of A) ⟶ X)
    (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A))) :
    ∃ z : EffectiveZeroCycle X, EffectiveZeroCycle.degree f z = Module.finrank k A := by
  have : IsFinite (q ≫ f) := by
    rw [hq]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have : IsFinite q := IsFinite.of_comp q f
  obtain ⟨z, hz⟩ := exists_effectiveZeroCycle_degree_finrank (k := k) (A := A)
  refine ⟨pushforwardCycle q z, ?_⟩
  rw [degree_pushforwardCycle, hq]
  exact hz

end AllCharacteristics
