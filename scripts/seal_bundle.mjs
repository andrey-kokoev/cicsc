#!/usr/bin/env node
import { readFile, writeFile } from "node:fs/promises";
import { createHash } from "node:crypto";
import { resolve } from "node:path";

async function main() {
  const filePath = process.argv[2];
  if (!filePath) {
    console.error("Usage: seal_bundle.mjs <bundle.json>");
    process.exit(1);
  }

  const content = await readFile(filePath, "utf-8");
  const bundle = JSON.parse(content);

  // Remove existing digest for hashing
  const { digest, ...rest } = bundle;
  
  const hash = createHash("sha256");
  hash.update(JSON.stringify(rest));
  const newDigest = hash.digest("hex");

  bundle.digest = newDigest;

  await writeFile(filePath, JSON.stringify(bundle, null, 2));
  console.log(`Sealed ${filePath} with digest ${newDigest}`);
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
