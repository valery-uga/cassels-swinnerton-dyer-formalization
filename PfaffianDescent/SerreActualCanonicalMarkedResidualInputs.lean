import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualGoodOpen
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceClosedFamily

/-! A bundle-independent record of actual marked incidence and canonical-fibre
data. Native geometry constructs this record before the Serre residual is
applied, keeping the two elaboration boundaries separate. -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

structure SerreActualCanonicalMarkedResidualInputs
    {F E L : Type u} [Field F] [Field E] [Field L] [Algebra F E]
    {X P Z I Cfg : Scheme.{u}}
    (x : X ⟶ Spec (.of F)) (pp : P ⟶ Spec (.of F))
    (zero : Z ⟶ pullback x pp) [IsClosedImmersion zero]
    [IsProper (zero ≫ pullback.snd x pp)]
    (i : I ⟶ X) (j : Spec (.of L) ⟶ X) where
  cfg : Cfg ⟶ Spec (.of F)
  marked : Fin 3 → (Cfg ⟶ X)
  hm : ∀ n, marked n ≫ x = cfg
  t : Spec (.of F) ⟶ P
  ht : t ≫ pp = 𝟙 _
  s : Spec (.of E) ⟶ serreThreePointSectionIncidence cfg x pp marked hm zero
  hW : s (IsLocalRing.closedPoint E) ∈ cubicClosedPointSerreFiniteZeroResidual_goodOpen
    (serreThreePointSectionIncidenceZeroFamily cfg x pp marked hm zero)
  hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg x pp marked hm zero =
    Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t
  n : Fin 3
  hout : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg x pp marked hm zero ≫
    marked n) (IsLocalRing.closedPoint E) ∉ Set.range i
  hpoint : (s ≫ serreThreePointSectionIncidenceToConfiguration cfg x pp marked hm zero ≫
    marked n) (IsLocalRing.closedPoint E) = j (IsLocalRing.closedPoint L)
  y : (pullback (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) : Scheme)
  hy : IsField ((pullback (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t)).presheaf.stalk y)
  hySurface : (pullback.fst (zero ≫ pullback.snd x pp)
    (Spec.map (CommRingCat.ofHom (algebraMap F E)) ≫ t) ≫ zero ≫
    pullback.fst x pp) y = j (IsLocalRing.closedPoint L)

end PfaffianDescent
