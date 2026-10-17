import PfaffianDescent.FlatLocalSerreNonzero214
import PfaffianDescent.CubicPointTraceFieldBaseChangeFlatStalkExt
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! Source candidate: an actual flat local-ring map preserves the unit local
Serre class. Properness and regularity of the image pair are derived. -/
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry IsLocalRing
open scoped nonZeroDivisors
namespace PfaffianDescent
universe u

theorem flatLocalRingHom_localSerreClass_ne_zero216
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [HasExt.{u + 1} (ModuleCat.{u} R)] [HasExt.{u + 1} (ModuleCat.{u} S)]
    (φ : R →+* S) [IsLocalHom φ] (hφ : φ.Flat) (f g c : R)
    (hf : f ∈ R⁰)
    (hg : Ideal.Quotient.mk (Ideal.span {f}) g ∈ (R ⧸ Ideal.span {f})⁰)
    (hfm : f ∈ maximalIdeal R) (hgm : g ∈ maximalIdeal R) (hc : IsUnit c) :
    cubicPointTraceFieldBaseChangeLocalExtMap φ hφ _ _ 2
      (localSerreExtTwoClass f g c hf hg) ≠ 0 := by
  apply actualFlatLocalSerreExtTwo_unit_ne_zero214 φ hφ f g c hf hg hc
  have hle : Ideal.span ({φ f, φ g} : Set S) ≤ maximalIdeal S := by
    apply Ideal.span_le.mpr
    intro r hr
    rcases Set.mem_insert_iff.mp hr with rfl | hr
    · exact map_nonunit φ f hfm
    · exact Set.mem_singleton_iff.mp hr ▸ map_nonunit φ g hgm
  intro h1
  exact (maximalIdeal.isMaximal S).ne_top ((Ideal.eq_top_iff_one _).mpr (hle h1))

theorem actualFlatStalk_localSerreClass_ne_zero216
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    [HasExt.{u + 1} (ModuleCat (Y.presheaf.stalk (f x)))]
    [HasExt.{u + 1} (ModuleCat (X.presheaf.stalk x))]
    (a b c : Y.presheaf.stalk (f x))
    (ha : a ∈ (Y.presheaf.stalk (f x))⁰)
    (hb : Ideal.Quotient.mk (Ideal.span {a}) b ∈
      ((Y.presheaf.stalk (f x)) ⧸ Ideal.span {a})⁰)
    (ham : a ∈ maximalIdeal (Y.presheaf.stalk (f x)))
    (hbm : b ∈ maximalIdeal (Y.presheaf.stalk (f x))) (hc : IsUnit c) :
    cubicPointTraceFieldBaseChangeLocalExtMap (f.stalkMap x).hom (Flat.stalkMap f x) _ _ 2
      (localSerreExtTwoClass a b c ha hb) ≠ 0 :=
  flatLocalRingHom_localSerreClass_ne_zero216 (f.stalkMap x).hom (Flat.stalkMap f x)
    a b c ha hb ham hbm hc

end PfaffianDescent
