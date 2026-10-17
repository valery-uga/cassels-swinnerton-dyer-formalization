import Mathlib.AlgebraicGeometry.Morphisms.Etale

noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

def cubicClosedPointSerreFiniteZeroResidual_etaleOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) : X.Opens :=
  ⨆ U : {U : X.Opens // Etale (U.ι ≫ f)}, U.1

theorem cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Etale ((cubicClosedPointSerreFiniteZeroResidual_etaleOpen f).ι ≫ f) := by
  let A := {U : X.Opens // Etale (U.ι ≫ f)}
  let W := cubicClosedPointSerreFiniteZeroResidual_etaleOpen f
  let U := fun a : A => W.ι ⁻¹ᵁ a.1
  have hU : ⨆ a, U a = ⊤ := by
    apply top_unique
    intro x hx'
    rw [Opens.mem_iSup]
    have hx := x.2
    change x.1 ∈ ⨆ a : A, a.1 at hx
    rw [Opens.mem_iSup] at hx
    exact hx
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @Etale) U hU
  intro a
  letI : Etale (a.1.ι ≫ f) := a.2
  have ha : a.1 ≤ W := le_iSup (fun a : A => a.1) a
  have he := congrArg (fun k => k ≫ f) (Scheme.Opens.isoOfLE_hom_ι ha)
  have ht : Etale ((Scheme.Opens.isoOfLE ha).hom ≫ a.1.ι ≫ f) := inferInstance
  simpa only [Category.assoc] using he ▸ ht

theorem cubicClosedPointSerreFiniteZeroResidual_le_etaleOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) [Etale (U.ι ≫ f)] :
    U ≤ cubicClosedPointSerreFiniteZeroResidual_etaleOpen f :=
  le_iSup (fun a : {U : X.Opens // Etale (U.ι ≫ f)} => a.1) ⟨U, inferInstance⟩

end PfaffianDescent
