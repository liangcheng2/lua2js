<script setup>
import { ref, computed } from 'vue'
import { lua2js, lua2ast } from '../lua2js.mjs'
import fs from "file-saver";

const jscodeRef = ref(null)
const showLuaAst = ref(false)
let luacode = ref(`\
local function snake_case_name(x, y)
  if x > 0 or y > 0then
    return nil, string.format('error: x is %s and y is %s', x, y)
  else
    return x + y
  end
end
console.log(string.format("hello %s", world))
console.log(string.format([[hello:
  you are multiple line %s]], world))
type(x+1)
table.concat(t, ",")
table_concat(t, ",")
table_concat({1,2,3}, ",")
t[#t+1] = 1
table_insert(t,1,a)
table.insert(t,1,a)
table_insert(t, 1)
table.insert(t, 1)
local array = {1,2}
local dict = {a=1, b=2}
Test = class {
  a = {1, 2}
}
local function foo(x, y)
  return x + y
end
local c = {a=1}
function c.foo(x, y)
  return x + y
end
function c.foo(self, x, y)
  return x + y + self.n
end
function c:foo(x, y)
  return x + y + self.n
end
local TestClass = class {
  p1 = 'Hi class property p1',
  p2 = 'Hi class property p2',
  static_func = function(x, y)
    return x + y
  end,
  class_method = function(cls)
    cls:say_class_hi()
  end,
  say_class_hi = function(cls)
    console.log(cls.p1)
  end,
  instance_method = function(self)
    self:say_instance_hi()
  end,
  say_instance_hi = function(self)
    console.log(this.p2)
  end
}
`)
// luacode.value = `function foo.bar(self)

// end
// local Child = class({
//   echo = function(self) end
// }, Parent)`
const jscode = computed(() => lua2js(luacode.value))
const luaast = computed(() => lua2ast(luacode.value))
const jscode_highlight_html = computed(() => hljs.highlight(jscode.value, { language: 'js' }).value)
function copyJs() {
  CopyToClipboard('jscode');
}
function saveJsAs() {
  fs.saveAs(new Blob([jscode.value]), "test.js")
}
function CopyToClipboard(containerid) {
  if (window.getSelection) {
    if (window.getSelection().empty) { // Chrome
      window.getSelection().empty();
    } else if (window.getSelection().removeAllRanges) { // Firefox
      window.getSelection().removeAllRanges();
    }
  } else if (document.selection) { // IE?
    document.selection.empty();
  }

  if (document.selection) {
    var range = document.body.createTextRange();
    range.moveToElementText(document.getElementById(containerid));
    range.select().createTextRange();
    document.execCommand("copy");
  } else if (window.getSelection) {
    var range = document.createRange();
    range.selectNode(document.getElementById(containerid));
    window.getSelection().addRange(range);
    document.execCommand("copy");
  }
}
</script>

<template>
  <div>
    <div class="row">
      <div class="col">
      </div>
    </div>
    <div class="row">
      <div class="col">
        <button @click="luacode = ''">clear textarea</button>
        <textarea rows="10" style="height:800px" class="form-control" :value="luacode"
          @input="luacode = $event.target.value"></textarea>
      </div>
      <div class="col">
        <div class="form-check-inline">
          <label class="form-check-label">
            <input @input="showLuaAst = !showLuaAst" :value="showLuaAst" type="checkbox" class="form-check-input" />show
            lua ast</label>
        </div>
        <div v-if="showLuaAst">
          <pre>{{ luaast }}</pre>
        </div>
        <div v-else>
          <highlightjs language='lua' :code="luacode" />
        </div>
      </div>
      <div class="col">
        <!-- <pre id="jscode2"><code class="language-javascript" v-html="jscode_highlight_html"></code></pre> -->
        <button @click="copyJs">copy js</button>
        <button @click="saveJsAs">save as</button>
        <highlightjs id="jscode" language='javascript' :code="jscode" />
      </div>
    </div>
  </div>
</template>

<style scoped>
.col {
  overflow: scroll;
}
</style>
