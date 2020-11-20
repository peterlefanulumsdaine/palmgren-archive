-- Erik Palmgren, September 1, 2019
-- Andreas Abel, November 20, 2020: converted to .agda file, determined Agda version

-- This development requires Agda ≥ 2.5.2, 600 MB free main memory
-- Tested successfully with the following versions (2020-11-20, contemporary macBook):
--
--   - 2.5.2: checks in 2min 15sec
--   - 2.5.3: checks in 2min 30sec
--
-- Unclear status with these versions:
--
--   - 2.5.4.2: killed after 90min (stuck on V-model-pt6)
--   - 2.6.0:   killed after  7min (stuck on V-model-pt6)
--   - 2.6.1:
--
-- Fails with: 2.4.2.x, 2.5.1.1 (and likely with older versions as well)

module README where

-- The following files are relevant for the setoid model
-- of extensional Martin-Löf type theory

-- general type and setoid constructions

import basic-types
import basic-setoids
import dependent-setoids
import subsetoids

-- Aczel's model of CZF

import iterative-sets
import iterative-sets-pt2
import iterative-sets-pt3
import iterative-sets-pt4
import iterative-sets-pt5
import iterative-sets-pt6
import iterative-sets-pt7
import iterative-sets-pt8

-- The model

import V-model-pt1
import V-model-pt2
import V-model-pt3
import V-model-pt4
import V-model-pt5  -- Takes some minutes to check
import V-model-pt6  -- Takes some minutes to check
import V-model-pt7
import V-model-pt8
import V-model-pt9
import V-model-pt10
import V-model-pt13
import V-model-pt11
import V-model-pt15

-- top module : all rules interpreted

import V-model-all-rules

-- Unfinished parts

import V-model-pt16    -- Quotient sets
