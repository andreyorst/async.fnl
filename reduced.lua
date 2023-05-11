--[[ MIT License

  Copyright (c) 2023 Andrey Listopadov

  Permission is hereby granted, free of charge, to any person obtaining a copy
  of this software and associated documentation files (the “Software”), to deal
  in the Software without restriction, including without limitation the rights
  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Software, and to permit persons to whom the Software is
  furnished to do so, subject to the following conditions:

  The above copyright notice and this permission notice shall be included in all
  copies or substantial portions of the Software.

  THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE. ]]

local lib_include_path = ...

if lib_include_path ~= "reduced" then
  local msg = [[Invalid usage of the Reduced library: required as "%s" not as "reduced".

The Reduced library must be required by callind require with the string "reduced" as the argument.
This ensures that all of the code across all libraries uses the same entry from package.loaded.]]
  error(msg:format(lib_include_path))
end

local Reduced = {
  __index = {unbox = function (x) return x[1] end},
  __fennelview = function (x, view, options, indent)
    return "#<reduced: " .. view(x[1], options, (11 + indent)) .. ">"
  end,
  __name = "reduced",
  __tostring = function (x) return ("reduced: " .. tostring(x[1])) end
}

local function reduced(value) return setmetatable({value}, Reduced) end
local function is_reduced(value) return rawequal(getmetatable(value), Reduced) end

return {reduced = reduced, ["reduced?"] = is_reduced, is_reduced = is_reduced}
