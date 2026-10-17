import AllCharacteristics.ProperCyclePushforward
import AllCharacteristics.EffectiveCycleToZeroCycle

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory AllCharacteristics
universe u
section
variable {X Y Z : Scheme.{u}}

/-- Pushforward of signed zero-cycles along a universally closed morphism, with actual residue degrees. -/
noncomputable def signedCyclePushforward (f : X ⟶ Y) [UniversallyClosed f] : ZeroCycle X →ₗ[ℤ] ZeroCycle Y :=
  Finsupp.linearCombination ℤ (fun x : closedPoints X =>
    Finsupp.single (universallyClosedPointMap f x) (f.residueDegree x.val : ℤ))

lemma signedCyclePushforward_single (f : X ⟶ Y) [UniversallyClosed f] (x : closedPoints X) (n : ℤ) :
    signedCyclePushforward f (Finsupp.single x n) =
      Finsupp.single (universallyClosedPointMap f x) (n * (f.residueDegree x.val : ℤ)) := by
  rw [signedCyclePushforward, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul]

/-- Signed proper pushforward preserves degree to the final base. -/
theorem signedCyclePushforward_degree (f : X ⟶ Y) [UniversallyClosed f] (g : Y ⟶ Z) (z : ZeroCycle X) :
    ZeroCycle.degree g (signedCyclePushforward f z) = ZeroCycle.degree (f ≫ g) z := by
  have h : (ZeroCycle.degree g).comp (signedCyclePushforward f) = ZeroCycle.degree (f ≫ g) := by
    apply Finsupp.lhom_ext
    intro x n
    simp only [LinearMap.comp_apply, signedCyclePushforward_single, ZeroCycle.degree_single,
      residueDegree_comp, Nat.cast_mul]
    change (n * (f.residueDegree x.val : ℤ)) * (g.residueDegree (f x.val) : ℤ) =
      n * ((g.residueDegree (f x.val) : ℤ) * (f.residueDegree x.val : ℤ))
    ring
  exact LinearMap.congr_fun h z

/-- Proper pushforward of signed zero-cycles is functorial. -/
theorem signedCyclePushforward_comp (f : X ⟶ Y) [UniversallyClosed f]
    (g : Y ⟶ Z) [UniversallyClosed g] :
    (signedCyclePushforward g).comp (signedCyclePushforward f) = signedCyclePushforward (f ≫ g) := by
  apply Finsupp.lhom_ext
  intro x n
  simp only [LinearMap.comp_apply, signedCyclePushforward_single, residueDegree_comp, Nat.cast_mul]
  have hp : universallyClosedPointMap g (universallyClosedPointMap f x) =
      universallyClosedPointMap (f ≫ g) x := Subtype.ext rfl
  rw [hp]
  congr 1
  change (n * (f.residueDegree x.val : ℤ)) * (g.residueDegree (f x.val) : ℤ) =
    n * ((g.residueDegree (f x.val) : ℤ) * (f.residueDegree x.val : ℤ))
  ring

end
end PfaffianDescent
