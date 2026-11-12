#!/usr/bin/env node
import { JSDOM } from "jsdom";

const THEMES = [
	"base",
	"dark",
	"default",
	"forest",
	"neutral",
	"neo",
	"neo-dark",
	"redux",
	"redux-dark",
	"redux-color",
	"redux-dark-color",
];

const TOKENS = [
	["bg", "background"],
	["surface", "mainBkg"],
	["fg", "primaryTextColor"],
	["muted", "secondaryTextColor"],
	["border", "primaryBorderColor"],
	["line", "lineColor"],
	["accent", "secondaryBorderColor"],
	["error", "errorBkgColor"],
	["warning", "noteBkgColor"],
	["success", "tertiaryColor"],
];

function fail(message) {
	process.stderr.write(`${message}\n`);
	process.exit(1);
}

async function loadThemes() {
	const { window } = new JSDOM("<body></body>");
	Object.defineProperty(globalThis, "document", {
		value: window.document,
		configurable: true,
	});
	const { themes_default } = await import(
		"./node_modules/mermaid/dist/chunks/mermaid.core/chunk-BG4553SI.mjs"
	);
	return themes_default;
}

function toHex(element, value, label) {
	if (typeof value !== "string" || value === "")
		fail(`${label}: not a colour value: ${String(value)}`);
	element.style.color = "";
	element.style.color = value;
	const computed =
		element.ownerDocument.defaultView.getComputedStyle(element).color;
	const match = /^rgba?\(([^)]*)\)$/.exec(computed);
	if (match === null) fail(`${label}: cannot resolve colour ${value}`);
	const parts = match[1].split(",").map((part) => part.trim());
	if (parts.length === 4 && Number(parts[3]) !== 1)
		fail(`${label}: colour has alpha: ${value}`);
	if (parts.length !== 3 && parts.length !== 4)
		fail(`${label}: unexpected colour ${value}`);
	const channels = parts.slice(0, 3).map((part) => Math.round(Number(part)));
	if (
		channels.some(
			(channel) => !Number.isInteger(channel) || channel < 0 || channel > 255,
		)
	) {
		fail(`${label}: channel out of range: ${value}`);
	}
	return `#${channels.map((channel) => channel.toString(16).padStart(2, "0")).join("")}`;
}

function readToken(variables, token, variable, element, theme) {
	if (!Object.hasOwn(variables, variable))
		fail(`${theme}: missing variable ${variable} for ${token}`);
	return toHex(element, variables[variable], `${theme}/${variable}`);
}

function readSeries(variables, index, element, theme) {
	const pie = `pie${index}`;
	const scale = `cScale${index}`;
	if (Object.hasOwn(variables, pie) && variables[pie] !== undefined) {
		return toHex(element, variables[pie], `${theme}/${pie}`);
	}
	if (Object.hasOwn(variables, scale) && variables[scale] !== undefined) {
		return toHex(element, variables[scale], `${theme}/${scale}`);
	}
	fail(`${theme}: missing variables ${pie} and ${scale}`);
}

async function main() {
	const themes = await loadThemes();
	const element = globalThis.document.createElement("div");
	globalThis.document.body.appendChild(element);
	const rows = [];
	for (const theme of THEMES) {
		const variables = themes[theme].getThemeVariables();
		const tokens = {};
		for (const [token, variable] of TOKENS) {
			tokens[token] = readToken(variables, token, variable, element, theme);
		}
		for (let index = 1; index <= 12; index += 1) {
			tokens[`series${index - 1}`] = readSeries(
				variables,
				index,
				element,
				theme,
			);
		}
		rows.push({ name: theme, tokens });
	}
	process.stdout.write(`${JSON.stringify(rows, null, 2)}\n`);
}

await main();
