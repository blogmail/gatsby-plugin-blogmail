[![Node.js CI](https://github.com/blogmail/gatsby-plugin-blogmail/workflows/Node.js%20CI/badge.svg?branch=master)](https://github.com/blogmail/gatsby-plugin-blogmail/actions?query=workflow%3A%22Node.js+CI%22) [![Node.js Package](https://github.com/blogmail/gatsby-plugin-blogmail/workflows/Node.js%20Package/badge.svg)](https://github.com/blogmail/gatsby-plugin-blogmail/actions?query=workflow%3A%22Node.js+Package%22) [![npm version](https://img.shields.io/npm/v/gatsby-plugin-blogmail.svg?style=flat-square)](https://www.npmjs.com/package/gatsby-plugin-blogmail)

# <img src="https://user-images.githubusercontent.com/16360374/60153578-90677300-9799-11e9-994a-d8f932d2efe1.png" height="38"/> Gatsby Plugin blogmail

A plugin that simplifies adding [blogmail](https://blogmail.co/) newsletters to your [Gatsby](https://www.gatsbyjs.org/) website

## Description

The goal of this plugin is to allow users to bring their content to life and cultivate engaged communities by integrating blogmail newsletters into their blazing-fast Gatsby websites. After struggling to integrate different components into my Gatsby site, creating an easily-configured plugin for the Gatsby ecosystem felt like a no-brainer.

## Install

```sh
yarn add gatsby-plugin-blogmail
```

or

```sh
npm install -S gatsby-plugin-blogmail
```

## Configure

Add the plugin to your `gatsby-config.js` file with your blogmail `newsletterId`. You must (at a minimum) provide a newsletter ID, and you can get one by signing up at https://blogmail.co/.

```js
// gatsby-config.js
module.exports = {
  plugins: [
    {
      resolve: `gatsby-plugin-blogmail`,
      options: {
        newsletterId: `your-newsletterId`,
      },
    },
  ],
}
```

## Usage

You can use the plugin as shown in this brief example:

```jsx
import Blogmail from "gatsby-plugin-blogmail"

const PostTemplate = () => {
  let blogmailConfig = {}
  return (
    <>
      <h1>{post.title}</h1>
      /* Post Contents */
      <Blogmail config={blogmailConfig} />
    </>
  )
}

export default PostTemplate
```
