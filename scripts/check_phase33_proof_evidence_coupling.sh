#!/usr/bin/env bash
set -euo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
OUT_PATH="${1:-${ROOT_DIR}/docs/pilot/phase33-proof-evidence-coupling.json}"
OUT_DIR="$(dirname "${OUT_PATH}")"

cd "${ROOT_DIR}"
mkdir -p "${OUT_DIR}"

INDEX_PATH="docs/pilot/phase33-proof-obligation-index.json"

node - "${OUT_PATH}" "${INDEX_PATH}" <<'NODE'
const fs = require('node:fs')
const path = require('node:path')

const outPath = process.argv[2]
const indexPath = process.argv[3]

// Load the proof-obligation index
let index
let indexLoadError = null
try {
  index = JSON.parse(fs.readFileSync(path.resolve(indexPath), 'utf8'))
} catch (e) {
  indexLoadError = e.message
}

const results = []
let overall = 'pass'

// If index can't be loaded, fail immediately
if (indexLoadError) {
  overall = 'fail'
  results.push({
    check: 'index_load',
    status: 'fail',
    error: indexLoadError,
    claim_class: null
  })
} else {
  const claimClasses = index?.proof_obligation_index?.claim_classes || []
  
  for (const cc of claimClasses) {
    const classId = cc.class_id
    const className = cc.claim_class
    
    // Check 1: Proof obligation must be defined
    if (!cc.proof_obligation) {
      overall = 'fail'
      results.push({
        check: 'proof_obligation_defined',
        status: 'fail',
        claim_class: classId,
        claim_class_name: className,
        reason: 'proof_obligation_not_defined'
      })
      continue
    }
    
    // Check 2: Required artifacts must exist
    const requiredArtifacts = cc.proof_obligation.required_artifacts || []
    const missingArtifacts = []
    for (const artifact of requiredArtifacts) {
      const artifactPath = path.resolve(artifact)
      if (!fs.existsSync(artifactPath)) {
        missingArtifacts.push(artifact)
      }
    }
    
    if (missingArtifacts.length > 0) {
      overall = 'fail'
      results.push({
        check: 'required_artifacts_exist',
        status: 'fail',
        claim_class: classId,
        claim_class_name: className,
        missing_artifacts: missingArtifacts
      })
      continue
    }
    
    // Check 3: Evidence binding must be defined
    if (!cc.evidence_binding) {
      overall = 'fail'
      results.push({
        check: 'evidence_binding_defined',
        status: 'fail',
        claim_class: classId,
        claim_class_name: className,
        reason: 'evidence_binding_not_defined'
      })
      continue
    }
    
    // Check 4: Evidence artifact must exist and have correct status
    const evidenceArtifact = cc.evidence_binding.artifact
    const statusField = cc.evidence_binding.status_field || 'overall'
    const passValue = cc.evidence_binding.pass_value || 'pass'
    
    let evidenceStatus = 'not_checked'
    let evidenceError = null
    
    try {
      const evidencePath = path.resolve(evidenceArtifact)
      if (!fs.existsSync(evidencePath)) {
        evidenceStatus = 'artifact_missing'
      } else {
        const evidence = JSON.parse(fs.readFileSync(evidencePath, 'utf8'))
        const actualStatus = evidence[statusField]
        if (actualStatus === passValue) {
          evidenceStatus = 'pass'
        } else {
          evidenceStatus = 'fail'
          evidenceError = `expected ${statusField}=${passValue}, got ${actualStatus}`
        }
      }
    } catch (e) {
      evidenceStatus = 'error'
      evidenceError = e.message
    }
    
    if (evidenceStatus !== 'pass') {
      overall = 'fail'
      results.push({
        check: 'evidence_binding_valid',
        status: 'fail',
        claim_class: classId,
        claim_class_name: className,
        evidence_artifact: evidenceArtifact,
        status_field: statusField,
        expected_value: passValue,
        actual_status: evidenceStatus,
        error: evidenceError
      })
    } else {
      results.push({
        check: 'claim_coupling_valid',
        status: 'pass',
        claim_class: classId,
        claim_class_name: className,
        evidence_artifact: evidenceArtifact
      })
    }
  }
  
  // Check 5: All claim classes must be in index
  if (claimClasses.length === 0) {
    overall = 'fail'
    results.push({
      check: 'claim_classes_present',
      status: 'fail',
      reason: 'no_claim_classes_in_index'
    })
  }
}

const report = {
  version: 'cicsc/phase33-proof-evidence-coupling-v1',
  timestamp_unix: Math.floor(Date.now() / 1000),
  phase: 33,
  checkbox: 'AX1.2',
  overall,
  policy: 'claims_without_proof_evidence_coupling_are_rejected',
  index_source: indexPath,
  total_checks: results.length,
  pass_count: results.filter(r => r.status === 'pass').length,
  fail_count: results.filter(r => r.status === 'fail').length,
  results
}

fs.writeFileSync(outPath, JSON.stringify(report, null, 2) + '\n', 'utf8')
console.log(`phase33 proof-evidence coupling report written: ${outPath}`)
process.exit(overall === 'pass' ? 0 : 1)
NODE
