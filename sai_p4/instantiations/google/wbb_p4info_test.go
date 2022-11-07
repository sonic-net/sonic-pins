package wbbp4info

import "testing"

func TestGet(t *testing.T) {
	p4info, err := Get()
	if err != nil {
		t.Errorf("unable to load p4info: %v", err)
	}
	if p4info == nil {
		t.Errorf("p4info is nil")
	}
}
