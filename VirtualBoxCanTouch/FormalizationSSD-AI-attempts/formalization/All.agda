{-# OPTIONS --cubical --guardedness #-}

module formalization.All where

-- Section 1: Stone duality
import formalization.StoneDuality.Preliminaries
import formalization.StoneDuality.AxiomDefs
import formalization.StoneDuality.Axioms
import formalization.StoneDuality.BooleanAlgebra
import formalization.StoneDuality.FinCofinAlgebra
import formalization.StoneDuality.NormalForms
import formalization.StoneDuality.Omniscience
import formalization.StoneDuality.OpenClosed

-- Section 2: Overtly discrete spaces
import formalization.OvertlyDiscrete.ODisc

-- Section 3: Stone spaces
import formalization.StoneSpaces.Topology
import formalization.StoneSpaces.ClosedInStone
import formalization.StoneSpaces.Profinite
import formalization.StoneSpaces.ProfiniteExport

-- Section 4: Compact Hausdorff spaces
import formalization.CompactHausdorff.CHaus
import formalization.CompactHausdorff.Interval

-- Section 5: Cohomology
import formalization.Cohomology.Disk
import formalization.Cohomology.CechCohomology
import formalization.Cohomology.ILocal
import formalization.Cohomology.Applications
