FROM node:20-slim

WORKDIR /app

# Copy repo structure
COPY . .

# Install dependencies (if any packages are present)
# find . -name "package.json" -exec npm install \; 
# For now, we assume a simple monorepo structure
# RUN npm install --workspaces

# Expose default runtime port
EXPOSE 3000

# Entrypoint to the CLI
ENTRYPOINT ["node", "cli/cicsc.mjs"]
CMD ["--help"]
