//==============================================================================
// LLM Adapter Interface
//
// BG1.5: Abstract provider interface for any LLM
// BG1.6: OpenAI provider implementation  
// BG1.7: Ollama provider implementation (local models)
//==============================================================================

export interface LLMMessage {
  role: "system" | "user" | "assistant"
  content: string
}

export interface LLMResponse {
  content: string
  model: string
  usage?: {
    promptTokens: number
    completionTokens: number
    totalTokens: number
  }
}

export interface LLMProvider {
  /**
   * Provider name
   */
  name: string

  /**
   * Send a chat completion request
   */
  chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse>

  /**
   * Check if provider is available
   */
  health(): Promise<boolean>
}

export interface LLMOptions {
  model?: string
  temperature?: number
  maxTokens?: number
  stop?: string[]
}

export type LLMProviderName = "openai" | "ollama" | "anthropic" | "local"

export interface LLMConfig {
  provider: LLMProviderName
  apiKey?: string
  baseUrl?: string
  defaultModel?: string
  maxTokens?: number
  temperature?: number
}

/**
 * Factory to create LLM providers
 */
export function createLLMProvider(config: LLMConfig): LLMProvider {
  switch (config.provider) {
    case "openai":
      return new OpenAIProvider(config)
    case "ollama":
      return new OllamaProvider(config)
    default:
      throw new Error(`Unknown LLM provider: ${config.provider}`)
  }
}

//==============================================================================
// OpenAI Provider Implementation (BG1.6)
//==============================================================================

export class OpenAIProvider implements LLMProvider {
  name = "openai"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.OPENAI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.openai.com/v1"
    this.defaultModel = config.defaultModel || "gpt-4o"
    
    if (!this.apiKey) {
      throw new Error("OpenAI API key required. Set OPENAI_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || this.defaultModel,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`OpenAI API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/models`, {
        headers: { "Authorization": `Bearer ${this.apiKey}` }
      })
      return response.ok
    } catch {
      return false
    }
  }
}

//==============================================================================
// Ollama Provider Implementation (BG1.7)
//==============================================================================

export class OllamaProvider implements LLMProvider {
  name = "ollama"
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.baseUrl = config.baseUrl || (typeof process !== "undefined" ? process.env.OLLAMA_BASE_URL : "") || "http://localhost:11434"
    this.defaultModel = config.defaultModel || "llama2"
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/api/chat`, {
      method: "POST",
      headers: { "Content-Type": "application/json" },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        stream: false,
        options: {
          temperature: options?.temperature ?? 0.7,
          num_predict: options?.maxTokens || 2048,
          stop: options?.stop
        }
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Ollama API error: ${response.status} - ${error}`)
    }

    const data = await response.json()

    return {
      content: data.message.content,
      model: data.model || this.defaultModel,
      usage: data.prompt_eval_count !== undefined || data.eval_count !== undefined ? {
        promptTokens: data.prompt_eval_count || 0,
        completionTokens: data.eval_count || 0,
        totalTokens: (data.prompt_eval_count || 0) + (data.eval_count || 0)
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const response = await fetch(`${this.baseUrl}/api/tags`)
      return response.ok
    } catch {
      return false
    }
  }
}

//==============================================================================
// Integration with Interview Engine
//==============================================================================

import { InterviewEngine } from "./interview-engine"

export class LLMInterviewEngine {
  private provider: LLMProvider
  private interview: InterviewEngine

  constructor(provider: LLMProvider) {
    this.provider = provider
    this.interview = new InterviewEngine()
  }

  /**
   * Process user input through LLM + interview engine
   */
  async process(input: string): Promise<string> {
    // First try local interview engine
    const localResponse = this.interview.processInput(input)
    if (localResponse) {
      return localResponse
    }

    // If interview complete, use LLM for refinement
    if (this.interview["state"]["currentStep"] === "CONFIRM") {
      return this.interview.getSummary()
    }

    // Otherwise get next question from interview
    return this.interview.getNextQuestion()
  }

  /**
   * Use LLM to enhance entity extraction from unstructured input
   */
  async extractEntities(unstructured: string): Promise<{
    entities: string[]
    states: Record<string, string[]>
    attributes: Record<string, string[]>
  }> {
    const prompt = `Extract entity definitions from this description. Return JSON with:
- entities: array of entity names
- states: object mapping entity names to their states
- attributes: object mapping entity names to their attributes (with types)

Input: ${unstructured}

Respond with valid JSON only.`

    const response = await this.provider.chat([
      { role: "system", content: "You extract structured entity definitions from natural language." },
      { role: "user", content: prompt }
    ])

    try {
      return JSON.parse(response.content)
    } catch {
      return { entities: [], states: {}, attributes: {} }
    }
  }

  /**
   * Use LLM to generate migration from natural language change request
   */
  async generateMigration(currentSpec: string, changeRequest: string): Promise<string> {
    const prompt = `Given this CICSC specification:

\`\`\`
${currentSpec}
\`\`\`

Generate a migration specification for this change request:

${changeRequest}

Respond with a migration spec in YAML format with: from_version, to_version, on_type, event_transforms.`

    const response = await this.provider.chat([
      { role: "system", content: "You generate CICSC migration specifications." },
      { role: "user", content: prompt }
    ])

    return response.content
  }
}
