# Kernel Embedding Examples

## Library Embedding

Use kernel exports directly from application code:

```ts
import { KernelMemoryBackend, verifyHistoryAgainstIr } from "../kernel/src/index"
```

Example file:

- `examples/kernel/library-embedding.ts`

## CLI Embedding

Use existing CLI wrapper as transport-level embedding:

```bash
node cli/cicsc.mjs verify --tenant t1 --server http://localhost
```

This demonstrates runtime/transport orchestration while kernel remains dependency-minimal.
