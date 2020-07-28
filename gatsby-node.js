var didRunAlready = false
let newsletterId = ""

exports.onPreInit = (_, pluginOptions) => {
  // Gatsby adds a pluginOptions that's not needed for this plugin
  delete pluginOptions.plugins
  newsletterId = pluginOptions.newsletterId

  if (didRunAlready) {
    throw new Error(
      "You can only have single instance of gatsby-plugin-blogmail in your gatsby-config.js"
    )
  }
  didRunAlready = true
}

exports.onCreateWebpackConfig = ({ plugins, actions }) => {
  var setWebpackConfig = actions.setWebpackConfig
  setWebpackConfig({
    plugins: [
      plugins.define({
        GATSBY_BLOGMAIL_NEWSLETTERID: JSON.stringify(newsletterId),
      }),
    ],
  })
}
