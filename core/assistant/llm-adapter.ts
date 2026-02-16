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

export type LLMProviderName = "openai" | "ollama" | "anthropic" | "openrouter" | "kimi" | "qwen" | "azure-openai" | "gemini" | "local"

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
    case "anthropic":
      return new AnthropicProvider(config)
    case "openrouter":
      return new OpenRouterProvider(config)
    case "kimi":
      return new KimiProvider(config)
    case "qwen":
      return new QwenProvider(config)
    case "azure-openai":
      return new AzureOpenAIProvider(config)
    case "gemini":
      return new GeminiProvider(config)
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
// Anthropic Provider Implementation (BG1.16)
//==============================================================================

export class AnthropicProvider implements LLMProvider {
  name = "anthropic"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.ANTHROPIC_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.anthropic.com/v1"
    this.defaultModel = config.defaultModel || "claude-3-5-sonnet-20241022"

    if (!this.apiKey) {
      throw new Error("Anthropic API key required. Set ANTHROPIC_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    // Anthropic uses a different message format
    const systemMessage = messages.find(m => m.role === "system")
    const userMessages = messages.filter(m => m.role !== "system").map(m => ({
      role: m.role === "assistant" ? "assistant" : "user",
      content: m.content
    }))

    const response = await fetch(`${this.baseUrl}/messages`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "x-api-key": this.apiKey,
        "anthropic-version": "2023-06-01"
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        max_tokens: options?.maxTokens || 4096,
        system: systemMessage?.content,
        messages: userMessages
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Anthropic API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const content = data.content[0]?.text || ""

    return {
      content,
      model: data.model,
      usage: data.usage ? {
        promptTokens: data.usage.input_tokens,
        completionTokens: data.usage.output_tokens,
        totalTokens: data.usage.input_tokens + data.usage.output_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      // Anthropic doesn't have a health endpoint, so we'll just check if we can authenticate
      const response = await fetch(`${this.baseUrl}/messages`, {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "x-api-key": this.apiKey,
          "anthropic-version": "2023-06-01"
        },
        body: JSON.stringify({
          model: this.defaultModel,
          max_tokens: 1,
          messages: [{ role: "user", content: "." }]
        })
      })
      // We expect this to succeed or fail with auth error
      return response.status !== 401
    } catch {
      return false
    }
  }
}

//==============================================================================
// OpenRouter Provider Implementation (BG1.17) - 100+ models
//==============================================================================

export class OpenRouterProvider implements LLMProvider {
  name = "openrouter"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.OPENROUTER_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://openrouter.ai/api/v1"
    this.defaultModel = config.defaultModel || "openai/gpt-4o"

    if (!this.apiKey) {
      throw new Error("OpenRouter API key required. Set OPENROUTER_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const response = await fetch(`${this.baseUrl}/chat/completions`, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "Authorization": `Bearer ${this.apiKey}`,
        "HTTP-Referer": "https://cicsc.dev",
        "X-Title": "CICSC"
      },
      body: JSON.stringify({
        model: options?.model || this.defaultModel,
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`OpenRouter API error: ${response.status} - ${error}`)
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
// Kimi Provider Implementation (BG1.18) - Moonshot AI
//==============================================================================

export class KimiProvider implements LLMProvider {
  name = "kimi"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.KIMI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://api.moonshot.cn/v1"
    this.defaultModel = config.defaultModel || "moonshot-v1-8k"

    if (!this.apiKey) {
      throw new Error("Kimi API key required. Set KIMI_API_KEY or pass apiKey in config.")
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
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Kimi API error: ${response.status} - ${error}`)
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
// Qwen Provider Implementation (BG1.19) - Alibaba
//==============================================================================

export class QwenProvider implements LLMProvider {
  name = "qwen"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.DASHSCOPE_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://dashscope.aliyuncs.com/compatible-mode/v1"
    this.defaultModel = config.defaultModel || "qwen-plus"

    if (!this.apiKey) {
      throw new Error("Qwen/DashScope API key required. Set DASHSCOPE_API_KEY or pass apiKey in config.")
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
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Qwen/DashScope API error: ${response.status} - ${error}`)
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
// Azure OpenAI Provider Implementation (BG1.20)
//==============================================================================

export class AzureOpenAIProvider implements LLMProvider {
  name = "azure-openai"
  private apiKey: string
  private baseUrl: string
  private deploymentName: string
  private apiVersion: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_ENDPOINT : "") || ""
    this.deploymentName = config.defaultModel || (typeof process !== "undefined" ? process.env.AZURE_OPENAI_DEPLOYMENT_NAME : "") || "gpt-4"
    this.apiVersion = "2024-02-15-preview"

    if (!this.apiKey || !this.baseUrl) {
      throw new Error("Azure OpenAI requires API key and endpoint. Set AZURE_OPENAI_API_KEY and AZURE_OPENAI_ENDPOINT.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    const url = `${this.baseUrl}/openai/deployments/${this.deploymentName}/chat/completions?api-version=${this.apiVersion}`
    
    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
        "api-key": this.apiKey
      },
      body: JSON.stringify({
        messages: messages.map(m => ({ role: m.role, content: m.content })),
        temperature: options?.temperature ?? 0.7,
        max_tokens: options?.maxTokens || 4096,
        stop: options?.stop
      })
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Azure OpenAI API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const choice = data.choices[0]

    return {
      content: choice.message.content,
      model: this.deploymentName,
      usage: data.usage ? {
        promptTokens: data.usage.prompt_tokens,
        completionTokens: data.usage.completion_tokens,
        totalTokens: data.usage.total_tokens
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const url = `${this.baseUrl}/openai/deployments/${this.deploymentName}?api-version=${this.apiVersion}`
      const response = await fetch(url, {
        headers: { "api-key": this.apiKey }
      })
      return response.ok
    } catch {
      return false
    }
  }
}

//==============================================================================
// Gemini Provider Implementation (BG1.21) - Google
//==============================================================================

export class GeminiProvider implements LLMProvider {
  name = "gemini"
  private apiKey: string
  private baseUrl: string
  private defaultModel: string

  constructor(config: LLMConfig) {
    this.apiKey = config.apiKey || (typeof process !== "undefined" ? process.env.GEMINI_API_KEY : "") || ""
    this.baseUrl = config.baseUrl || "https://generativelanguage.googleapis.com/v1beta"
    this.defaultModel = config.defaultModel || "gemini-1.5-pro"

    if (!this.apiKey) {
      throw new Error("Gemini API key required. Set GEMINI_API_KEY or pass apiKey in config.")
    }
  }

  async chat(messages: LLMMessage[], options?: LLMOptions): Promise<LLMResponse> {
    // Gemini uses a different message format
    const contents = messages
      .filter(m => m.role !== "system")
      .map(m => ({
        role: m.role === "assistant" ? "model" : "user",
        parts: [{ text: m.content }]
      }))

    const systemInstruction = messages.find(m => m.role === "system")?.content

    const url = `${this.baseUrl}/models/${options?.model || this.defaultModel}:generateContent?key=${this.apiKey}`
    
    const body: any = {
      contents,
      generationConfig: {
        temperature: options?.temperature ?? 0.7,
        maxOutputTokens: options?.maxTokens || 4096,
        stopSequences: options?.stop
      }
    }

    if (systemInstruction) {
      body.systemInstruction = {
        parts: [{ text: systemInstruction }]
      }
    }

    const response = await fetch(url, {
      method: "POST",
      headers: {
        "Content-Type": "application/json"
      },
      body: JSON.stringify(body)
    })

    if (!response.ok) {
      const error = await response.text()
      throw new Error(`Gemini API error: ${response.status} - ${error}`)
    }

    const data = await response.json()
    const content = data.candidates?.[0]?.content?.parts?.[0]?.text || ""

    return {
      content,
      model: this.defaultModel,
      usage: data.usageMetadata ? {
        promptTokens: data.usageMetadata.promptTokenCount,
        completionTokens: data.usageMetadata.candidatesTokenCount,
        totalTokens: data.usageMetadata.totalTokenCount
      } : undefined
    }
  }

  async health(): Promise<boolean> {
    try {
      const url = `${this.baseUrl}/models?key=${this.apiKey}`
      const response = await fetch(url)
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
