import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeEtaleOpen

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_mem_etaleOpen_of_openImmersion
    {A X Y : Scheme.{u}} (a : A ⟶ X) [IsOpenImmersion a]
    (g : X ⟶ Y) [Etale (a ≫ g)] (z : A) :
    a z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g := by
  let U := a.opensRange
  let e : A ≅ U := IsOpenImmersion.isoOfRangeEq a U.ι (by
    change Set.range a = Set.range U.ι
    rw [Scheme.Opens.range_ι]
    rfl)
  have he : e.inv ≫ a = U.ι := IsOpenImmersion.isoOfRangeEq_inv_fac a U.ι _
  have ht : Etale (e.inv ≫ a ≫ g) := inferInstance
  haveI : Etale (U.ι ≫ g) := by
    simpa only [← Category.assoc, he] using ht
  apply cubicClosedPointSerreFiniteZeroResidual_le_etaleOpen g U
  exact ⟨z, rfl⟩

theorem cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_under_openImmersion
    {A X Y : Scheme.{u}} (a : A ⟶ X) [IsOpenImmersion a]
    (g : X ⟶ Y) (z : A)
    (hz : z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen (a ≫ g)) :
    a z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g := by
  let W := cubicClosedPointSerreFiniteZeroResidual_etaleOpen (a ≫ g)
  letI : Etale (W.ι ≫ (a ≫ g)) :=
    cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale (a ≫ g)
  haveI : Etale ((W.ι ≫ a) ≫ g) := by simpa only [Category.assoc] using inferInstanceAs (Etale (W.ι ≫ (a ≫ g)))
  exact cubicClosedPointSerreFiniteZeroResidual_mem_etaleOpen_of_openImmersion
    (W.ι ≫ a) g ⟨z, hz⟩

 theorem cubicClosedPointSerreFiniteZeroResidual_etaleOpen_mem_postcomp
    {X Y T : Scheme.{u}} (g : X ⟶ Y) (b : Y ⟶ T) [Etale b]
    (z : X) (hz : z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen g) :
    z ∈ cubicClosedPointSerreFiniteZeroResidual_etaleOpen (g ≫ b) := by
  let W := cubicClosedPointSerreFiniteZeroResidual_etaleOpen g
  letI : Etale (W.ι ≫ g) :=
    cubicClosedPointSerreFiniteZeroResidual_etaleOpen_etale g
  haveI : Etale (W.ι ≫ (g ≫ b)) := by
    simpa only [← Category.assoc] using inferInstanceAs (Etale ((W.ι ≫ g) ≫ b))
  exact cubicClosedPointSerreFiniteZeroResidual_le_etaleOpen (g ≫ b) W hz

end PfaffianDescent
