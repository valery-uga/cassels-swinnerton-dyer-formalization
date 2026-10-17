import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Extensive

/-! # Base change of constant covers and actual kernel pairs

Finite constant coproducts commute with base change even when the indexing
type has a different universe. A Cartesian change of a quotient morphism
induces a Cartesian square on its actual kernel pair and first projection.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace AllCharacteristics
universe u v

/-- Finite constant coproducts form an actual Cartesian square under base change. -/
lemma isPullback_sigmaMap_constant
    {ι : Type v} [Finite ι] [Small.{u} ι] {T S : Scheme.{u}} (g : T ⟶ S) :
    IsPullback (CategoryTheory.Limits.Sigma.map (f := fun _ : ι => T) (g := fun _ : ι => S) fun _ => g)
      (Sigma.desc (fun _ : ι => 𝟙 T)) (Sigma.desc (fun _ : ι => 𝟙 S)) g := by
  have hu := FinitaryPreExtensive.isUniversal_finiteCoproducts
    (coproductIsCoproduct (fun _ : ι => S))
  have h := hu.isPullback_of_isColimit_left (fun _ : ι => 𝟙 S)
    (Sigma.desc (fun _ : ι => 𝟙 S)) g (fun _ : ι => 𝟙 T) (fun _ : ι => g)
    (fun _ => IsPullback.of_horiz_isIso (by simp))
    (coproductIsCoproduct (fun _ : ι => T)) (fun _ => Sigma.ι_desc _ _)
  convert h.flip using 1 <;> rfl

/-- The actual induced map between kernel pairs of a Cartesian pair of morphisms. -/
noncomputable def kernelPairBaseChangeMap
    {U X V Y : Scheme.{u}} {i : U ⟶ X} {r : U ⟶ V} {q : X ⟶ Y} {j : V ⟶ Y}
    (h : IsPullback i r q j) : pullback r r ⟶ pullback q q :=
  pullback.map r r q q i i j h.w.symm h.w.symm

/-- The induced kernel-pair map preserves the first projection. -/
lemma kernelPairBaseChangeMap_fst
    {U X V Y : Scheme.{u}} {i : U ⟶ X} {r : U ⟶ V} {q : X ⟶ Y} {j : V ⟶ Y}
    (h : IsPullback i r q j) :
    kernelPairBaseChangeMap h ≫ pullback.fst q q = pullback.fst r r ≫ i :=
  pullback.lift_fst _ _ _

/-- The induced kernel-pair map preserves the second projection. -/
lemma kernelPairBaseChangeMap_snd
    {U X V Y : Scheme.{u}} {i : U ⟶ X} {r : U ⟶ V} {q : X ⟶ Y} {j : V ⟶ Y}
    (h : IsPullback i r q j) :
    kernelPairBaseChangeMap h ≫ pullback.snd q q = pullback.snd r r ≫ i :=
  pullback.lift_snd _ _ _

/-- The induced kernel-pair map is Cartesian over the first source projection. -/
lemma isPullback_kernelPairBaseChangeMap
    {U X V Y : Scheme.{u}} {i : U ⟶ X} {r : U ⟶ V} {q : X ⟶ Y} {j : V ⟶ Y}
    (h : IsPullback i r q j) :
    IsPullback (kernelPairBaseChangeMap h) (pullback.fst r r) (pullback.fst q q) i := by
  have ho : IsPullback (kernelPairBaseChangeMap h ≫ pullback.snd q q)
      (pullback.fst r r) q (i ≫ q) := by
    rw [kernelPairBaseChangeMap_snd, h.w]
    exact (IsPullback.of_hasPullback r r).flip.paste_horiz h
  exact ho.of_right (kernelPairBaseChangeMap_fst h) (IsPullback.of_hasPullback q q).flip

end AllCharacteristics
