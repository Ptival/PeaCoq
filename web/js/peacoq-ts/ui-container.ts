@component("ui-container")

@style(`
.ui-container {
  .background-color: red;
}
`)

@template(`
<div class="ui-container">
  <content></content>
</div>
`)

class UIContainer extends polymer.Base {
  constructor() {
    super();
  }
}

UIContainer.register();
