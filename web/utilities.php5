<?
  function to_js($v) // no escape & co
  {
    switch (gettype($v))
    {
      case 'boolean':
        return $v ? 'true' : 'false';
      case 'integer':
      case 'double':
      case 'float':
        return "$v";
      case 'string':
        return "'$v'";
      case 'NULL':
        return 'null';
      case 'array':
        $r = '{';
        foreach ($v as $k => $w)
          $r .= "'$k': " . to_js($w) . ',';
        $r .= '}';
        return $r;
     }
     return 'undefined' . ' /* ' . gettype($v) . ' */';
  }

  function var_to_js($n, $v)
  {
    return 'var ' . $n . ' = ' . to_js($v) . ";\n";
  }

  function dir_tree($name, $prefix, $filter_ext)
  {
    $r = array( 'n' => '', 'f' => array(), 'd' => array(), 'of' => array() );
    $files = scandir($prefix . $name);
    foreach ($files as $f)
    {
      if ($f[0] == '.')
        continue;
      $loc = $name == '' ? $f : $name . '/' . $f;
      $full = $prefix . $loc;
      if (is_dir($full))
      {
        $r['d'][$f] = dir_tree($loc, $prefix, $filter_ext);
        $r['d'][$f]['n'] = $loc;
      }
      else if (isset($filter_ext[pathinfo($full, PATHINFO_EXTENSION)]))
        $r['f'][$f] = $loc;
      else
        $r['of'][$f] = $full;
    }
    return $r;
  }
?>
