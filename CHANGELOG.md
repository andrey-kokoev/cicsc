# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [v1.2.0] - 2026-02-15

### Added
- OAuth integration (Phase BH)
- RBAC engine (Phase BI)
- Audit logging (Phase BJ)

## [v1.1.0] - 2026-02-15

### Added
- Conversational Spec Assistant (Phase BG)
- Natural language to Spec DSL translation
- Interactive interview engine
- Iterative refinement interface

## [v1.0.0] - 2026-02-15

### Added
- Spec DSL surface language
- Bundle Registry (R2/KV storage)
- Migration System with replay verification
- Postgres Adapter with conformance testing
- Complete documentation and examples
- v1.0 integration and release


## [v1.2.1] - $(date +%Y-%m-%d)

### Added
- Microsoft OAuth adapter (Entra ID / Azure AD support)

## [v1.3.0] - $(date +%Y-%m-%d)

### Added
- Blob Storage Support (Phase BK)
  - New 'blob' type in Spec DSL with constraints (maxSize, allowedTypes)
  - R2 adapter (Cloudflare) with S3-compatible API
  - S3 adapter (AWS) with presigned URL generation
  - Runtime integration for uploads, metadata storage, and secure downloads
  - Storage backend configuration in Spec

### Changed
- Extended Spec DSL parser to support blob declarations
- Added storage adapters framework for extensibility
