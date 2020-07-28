module.exports = {
  parser: "babel-eslint",
  extends: ["plugin:prettier/recommended", "prettier"],
  plugins: ["prettier"],
  rules: {
    "capitalized-comments": "off",
    "prettier/prettier": "error",
  },
  env: {
    jest: true,
    node: true,
  },
  globals: {
    GATSBY_BLOGMAIL_NEWSLETTERID: true,
  },
}
