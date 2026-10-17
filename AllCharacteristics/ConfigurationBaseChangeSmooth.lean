import AllCharacteristics.RelativeConfigurationOpen
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Smoothness of original configurations after base change

Pullback associativity and pasting prove the assertions for the original
ordered powers and configuration opens. No comparison with a separately
constructed power or symmetric product is assumed.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u

/-- A relative product becomes smooth after a base change that makes both factors smooth. -/
lemma smooth_pullback_relativeProduct
    {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ S) (g : T ⟶ S)
    [Smooth (pullback.snd f g)] [Smooth (pullback.snd h g)] :
    Smooth (pullback.snd (pullback.snd f h ≫ h) g) := by
  have hinner : Smooth (pullback.snd f (pullback.fst h g ≫ h)) := by
    rw [pullback.condition]
    have hs : Smooth ((pullbackLeftPullbackSndIso f g (pullback.snd h g)).inv ≫
        pullback.snd (pullback.snd f g) (pullback.snd h g)) := by
      infer_instance
    simpa only [pullbackLeftPullbackSndIso_inv_snd_snd] using hs
  have hs : Smooth ((pullbackAssoc f h h g).hom ≫
      pullback.snd f (pullback.fst h g ≫ h) ≫ pullback.snd h g) := by
    infer_instance
  simpa only [pullbackAssoc_hom_snd_snd] using hs

/-- Restricting the source to an open preserves smoothness after the original base change. -/
lemma smooth_pullback_comp_openImmersion
    {X' X S T : Scheme.{u}} (i : X' ⟶ X) [IsOpenImmersion i]
    (f : X ⟶ S) (g : T ⟶ S) [Smooth (pullback.snd f g)] :
    Smooth (pullback.snd (i ≫ f) g) := by
  have hs : Smooth ((pullbackRightPullbackFstIso f g i).inv ≫
      pullback.snd i (pullback.fst f g) ≫ pullback.snd f g) := by
    infer_instance
  simpa only [pullbackRightPullbackFstIso_inv_snd_snd] using hs

/-- The actual ordered power becomes smooth whenever the original family does after base change. -/
lemma smooth_pullback_orderedFamilyPower
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    [Smooth (pullback.snd f g)] (n : ℕ) :
    Smooth (pullback.snd (orderedFamilyPowerOver f n).hom g) := by
  induction n with
  | zero =>
    change Smooth (pullback.snd (𝟙 S) g)
    infer_instance
  | succ n ih =>
    have := ih
    change Smooth (pullback.snd (pullback.fst f (orderedFamilyPowerOver f n).hom ≫ f) g)
    rw [pullback.condition]
    exact smooth_pullback_relativeProduct f (orderedFamilyPowerOver f n).hom g

/-- The actual distinct-configuration open becomes smooth after the same base change. -/
lemma smooth_pullback_orderedFamilyConfiguration
    {X S T : Scheme.{u}} (f : X ⟶ S) [IsSeparated f] (g : T ⟶ S)
    [Smooth (pullback.snd f g)] (n : ℕ) :
    Smooth (pullback.snd (orderedFamilyConfigurationOver f n).hom g) := by
  have := smooth_pullback_orderedFamilyPower f g n
  exact smooth_pullback_comp_openImmersion (orderedFamilyConfigurationOpen f n).ι
    (orderedFamilyPowerOver f n).hom g

end AllCharacteristics
