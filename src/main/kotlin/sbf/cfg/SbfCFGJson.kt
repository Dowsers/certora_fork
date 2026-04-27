/*
 *     The Certora Prover
 *     Copyright (C) 2026  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package sbf.cfg

import datastructures.stdcollections.*
import kotlinx.serialization.json.*

private val prettyJson = Json { prettyPrint = true }

/** Dump a [SbfCFG] to a pretty-printed JSON string.
 *
 * Format:
 * ```json
 * {
 *   "name": "<function name>",
 *   "entry": "<entry label>",
 *   "exit": "<exit label>",
 *   "blocks": [
 *     {
 *       "label": "<block label>",
 *       "predecessors": ["<label>", ...],
 *       "successors": ["<label>", ...],
 *       "instructions": [
 *         { "inst": "<SbfInstruction.toString()>", "meta": <metaId> },
 *         { "inst": "<SbfInstruction.toString()>" },
 *         ...
 *       ]
 *     },
 *     ...
 *   ],
 *   "metas": {
 *     "<metaId>": { "<key>": <value>, ... },
 *     ...
 *   }
 * }
 * ```
 *
 * Each instruction is a JSON object with an `"inst"` field holding [SbfInstruction.toString]
 * and, when [MetaData] is non-empty, a numeric `"meta"` field whose value is the key into
 * the top-level `"metas"` object.
 *
 * Metadata values are encoded as:
 * - Flag (Unit) keys  -> `true`
 * - Boolean keys      -> `true` / `false`
 * - Numeric keys      -> JSON number (unquoted)
 * - Everything else   -> JSON string via [toString]
 */
fun SbfCFG.toJson(): String {
    var nextMetaId = 0
    val metaJsonToId = mutableMapOf<JsonObject, Int>()  // dedup key: JSON repr of metadata
    val metas = mutableMapOf<Int, JsonObject>()

    fun metaIdFor(metaData: MetaData): Int? {
        if (metaData.entries.none()) {
            return null
        }
        val jsonObj = metaDataToJsonObject(metaData)
        return metaJsonToId.getOrPut(jsonObj) {
            val id = nextMetaId++
            metas[id] = jsonObj
            id
        }
    }

    val blocksArray = buildJsonArray {
        for (block in getBlocks().values) {
            add(buildJsonObject {
                put("label", block.getLabel().toString())
                put("predecessors", buildJsonArray {
                    block.getPreds().forEach { add(it.getLabel().toString()) }
                })
                put("successors", buildJsonArray {
                    block.getSuccs().forEach { add(it.getLabel().toString()) }
                })
                put("instructions", buildJsonArray {
                    for (inst in block.getInstructions()) {
                        val metaId = metaIdFor(inst.metaData)
                        add(buildJsonObject {
                            put("inst", inst.toString())
                            if (metaId != null) {
                                put("meta", metaId)
                            }
                        })
                    }
                })
            })
        }
    }

    val metasObject = buildJsonObject {
        metas.forEachEntry { (id, jsonObj) -> put(id.toString(), jsonObj) }
    }

    val root = buildJsonObject {
        put("name", getName())
        put("entry", getEntry().getLabel().toString())
        put("exit", getExit().getLabel().toString())
        put("blocks", blocksArray)
        put("metas", metasObject)
    }

    return prettyJson.encodeToString(JsonElement.serializer(), root)
}

private fun metaDataToJsonObject(metaData: MetaData): JsonObject {
    return buildJsonObject {
        for ((key, value) in metaData.entries) {
            val jsonValue: JsonElement = when (value) {
                is Unit    -> JsonPrimitive(true)
                is Boolean -> JsonPrimitive(value)
                is Int     -> JsonPrimitive(value)
                is Long    -> JsonPrimitive(value)
                is ULong   -> JsonPrimitive(value.toLong())
                is String  -> JsonPrimitive(value)
                else       -> JsonPrimitive(value.toString())
            }
            put(key.name, jsonValue)
        }
    }
}
