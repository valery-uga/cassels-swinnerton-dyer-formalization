import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualSeedFibreSurface
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualMarkedFibreSurface

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false

theorem cubicClosedPointSerreFiniteZeroResidual_chosenMarked_mem_surface_range
    {S B X P Z D T : Scheme.{u}}
    (cfg : B ⟶ S) (base : X ⟶ S) (p : P ⟶ S)
    (marked : Fin 3 → (B ⟶ X)) (hm : ∀ n, marked n ≫ base = cfg)
    (zero : Z ⟶ pullback base p) [IsClosedImmersion zero]
    (s : T ⟶ serreThreePointSectionIncidence cfg base p marked hm zero)
    (t : S ⟶ P) (d : D ⟶ S) (c : D ⟶ X)
    (v : D ≅ pullback (zero ≫ pullback.snd base p) t)
    (hv : v.hom ≫ pullback.snd (zero ≫ pullback.snd base p) t = d)
    (hvc : v.hom ≫ pullback.fst (zero ≫ pullback.snd base p) t ≫
      zero ≫ pullback.fst base p = c)
    (r : T ⟶ S)
    (hsp : s ≫ serreThreePointSectionIncidenceToParameters cfg base p marked hm zero = r ≫ t)
    (n : Fin 3) (u : T) :
    (s ≫ serreThreePointSectionIncidenceToConfiguration cfg base p marked hm zero ≫ marked n) u ∈
      Set.range c := by
  let g := serreThreePointSectionIncidenceZeroFamily cfg base p marked hm zero
  let j := serreIncidenceMarkedZeroSection cfg base p marked hm zero n
  let m := cubicClosedPointSerreFiniteZeroResidual_markedFibreSection g j
    (serreIncidenceMarkedZeroSection_toIncidence cfg base p marked hm zero n) s
  let e := serreIncidenceSeedCanonicalFibreIso cfg base p marked hm zero s t d v hv r hsp
  let q := pullback.fst g s ≫ pullback.fst (zero ≫ pullback.snd base p)
    (serreThreePointSectionIncidenceToParameters cfg base p marked hm zero) ≫
    zero ≫ pullback.fst base p
  have he : e.hom ≫ q = pullback.fst d r ≫ c :=
    cubicClosedPointSerreFiniteZeroResidual_seedFibreIso_hom_surface
      cfg base p marked hm zero s t d c v hv hvc r hsp
  have hei : e.inv ≫ pullback.fst d r ≫ c = q := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  have hmproj : m ≫ q = s ≫ serreThreePointSectionIncidenceToConfiguration
      cfg base p marked hm zero ≫ marked n :=
    cubicClosedPointSerreFiniteZeroResidual_markedFibreSection_surface
      cfg base p marked hm zero s n
  refine ⟨pullback.fst d r (e.inv (m u)), ?_⟩
  calc
    _ = (e.inv ≫ pullback.fst d r ≫ c) (m u) := by simp only [Scheme.Hom.comp_apply]
    _ = q (m u) := congrArg (fun f : pullback g s ⟶ X => f (m u)) hei
    _ = (m ≫ q) u := by simp only [Scheme.Hom.comp_apply]
    _ = _ := congrArg (fun f => f u) hmproj

end PfaffianDescent
